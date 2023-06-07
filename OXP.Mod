(* begin-package-description

**Package Overview**

Integrated Oberon uses a one-pass compiler with four parts, each depending on the next for functionaltiy:

 * A recursive-descent parser of the Oberon language, OXP
 * A generator of target-generic opcodes (RISC5), OXG
 * A generator of target-specific opcodes (RISC5, x86_64, aarch64, arm, riscv64, riscv32), OXX
 * A symbol table and frame tracker, OXB
 * A scanner and tokenizer, OXS

In addition, several tools link and examine the binary modules produced by the compiler:

 * A linker and loader, Linker
 * A tool for examining modules, OXTool

**Package Usage**

To compile the inner core::

   OXP.Compile Kernel.Mod/s, Filedir.Mod/s, Files.Mod/s, Modules.Mod/s ~

To link the inner core modules into a bootable binary::

   Linker.Link Modules ~

To Install the binary into the boot region of the current disk image::

   Linker.Load Modules.bin ~

To compile an example module::

   OXP.Compile Sierpinski.Mod ~

To examine the symbol file of the compiled example::

   OXTool.DecSym Sierpinski.smb

To Examine the binary of the compiled example::

   OXTool.DecObj Sierpinski.rsc

end-package-description *)

(* begin-module-short-description
implements a recursive-descent parser for the Oberon language.
end-module-short-description *)

(* begin-module-use-description

Module OXP reads the source code of an Oberon program and produces an executable binary module.

end-module-use-description *)
(* begin-module-develop-description

(N. Wirth 1.7.97 / 8.3.2020 Oberon compiler for RISC in Oberon-07, C. Perkins 2020/21 annotated and extended)

**OXP** implements a one-pass recursive descent parser for the language Oberon.

The structure of the parser is derived from the structure of the language, with constituent parts of the language
(e.g. Module, Procedure, Type, Expression, Term, Parameter) represented by a procedure of that name, invoked from the
encompassing construct. Each procedure consumes and validates a part of the program source text while populating the
symbol table and execution context and also generating machine code faithfully representing that language construct.

This module (OXP) relies on module OXG for code generation, OXB for the symbol table, execution context tracking and reserved words, and OXS
for lexical parsing and built-in type identification.

end-module-develop-description *)
MODULE OXP; (*N. Wirth 1.7.97 / 8.3.2020  Oberon compiler for RISC in Oberon-07*)
  IMPORT Out, Texts, OXS, OXB, OXG; (*Oberon*)
  (*Author: Niklaus Wirth, 2014.
    Parser of Oberon-RISC compiler. Uses Scanner OXS to obtain symbols (tokens),
    OXB for definition of data structures and for handling import and export, and
    OXG to produce binary code. ORP performs type checking and data allocation.
    Parser is target-independent, except for part of the handling of allocations.*)

  CONST

  TYPE
    PtrBase = POINTER TO PtrBaseDesc;
    PtrBaseDesc = RECORD  (*list of names of pointer base types*)
      name: OXS.Ident; type: OXB.Type; next: PtrBase
    END ;
    FileName* = ARRAY 32 OF CHAR;
    Options* = ARRAY 8 OF CHAR;

  VAR
    sym: INTEGER;   (*last symbol read*)
    dc: INTEGER;    (*data counter*)
    level, exno, version: INTEGER;
    newSF: BOOLEAN;  (*option flag*)
    ccARCH, ccWordsize, ccStackalign: INTEGER;
    expression: PROCEDURE (VAR x: OXG.Item);  (*to avoid forward reference*)
    Type: PROCEDURE (VAR type: OXB.Type);
    FormalType: PROCEDURE (VAR typ: OXB.Type; dim: INTEGER);
    modid: OXS.Ident;
    pbsList: PtrBase;   (*list of names of pointer base types*)
    dummy: OXB.Object;
    W: Texts.Writer;
    kw: OXS.Keyword;

  (* begin-procedure-description
---
**Emit** Outputs text to the console.
  end-procedure-description *)
  PROCEDURE Emit(s: ARRAY OF CHAR);
    VAR ss: ARRAY 128 OF CHAR;
  BEGIN ss:=s; Out.String(ss);
  END Emit;

  (* begin-procedure-description
---
**EmitLn** Outputs text to the console with newline.
  end-procedure-description *)
  PROCEDURE EmitLn;
  BEGIN Out.Ln
  END EmitLn;

  (* begin-procedure-description
---
**Mark** reports an error to the Oberon system log.
  end-procedure-description *)
  PROCEDURE Mark*(msg: ARRAY OF CHAR);
    VAR p: INTEGER; ss: ARRAY 32 OF CHAR;
  BEGIN p := OXS.Pos();
    IF (p > OXS.errpos) & (OXS.errcnt < 25) THEN
      Emit(" pos ");
      Out.Int(p, 1); Emit( " " );
      ss:= msg; Emit( ss ); EmitLn
    END ;
    OXS.BumpErr(p+4)
(*    INC(OXS.errcnt); OXS.errpos := p + 4 *)
  END Mark;


(* begin-section-description
## ---------- Tests
  end-section-description *)

  (* begin-procedure-description
---
**Check** marks an error if the current symbol does not match the expeted symbol.
  end-procedure-description *)
  PROCEDURE Check(s: INTEGER; msg: ARRAY OF CHAR);
  BEGIN
    IF sym = s THEN OXS.Get(sym) ELSE Mark(msg) END
  END Check;

  (* begin-procedure-description
---
**Qualident** generates a reference to a previously defined item if possible otherwise an error is marked.
  end-procedure-description *)
  PROCEDURE qualident(VAR obj: OXB.Object);
  BEGIN obj := OXB.thisObj(); OXS.Get(sym);
    IF obj = NIL THEN Mark("undef"); obj := dummy END ;
    IF (sym = OXS.period) & (obj.class = OXB.Mod) THEN
      OXS.Get(sym);
      IF sym = OXS.ident THEN obj := OXB.thisimport(obj); OXS.Get(sym);
        IF obj = NIL THEN Mark("undef"); obj := dummy END
      ELSE Mark("identifier expected"); obj := dummy
      END
    END
  END qualident;

  (* begin-procedure-description
---
**CheckBool** marks an error if the item is not a boolean.
  end-procedure-description *)
  PROCEDURE CheckBool(VAR x: OXG.Item);
  BEGIN
    IF x.type.form # OXB.Bool THEN Mark("not Boolean"); x.type := OXB.boolType END
  END CheckBool;

  (* begin-procedure-description
---
**CheckInt** marks an error if the item is not an Int.
  end-procedure-description *)
  PROCEDURE CheckInt(VAR x: OXG.Item);
  BEGIN
    IF x.type.form # OXB.Int THEN Mark("not Integer"); x.type := OXB.intType END
  END CheckInt;

  (* begin-procedure-description
---
**CheckReal** marks an error if the item is not a Real.
  end-procedure-description *)
  PROCEDURE CheckReal(VAR x: OXG.Item);
  BEGIN
    IF x.type.form # OXB.Real THEN Mark("not Real"); x.type := OXB.realType END
  END CheckReal;

  (* begin-procedure-description
---
**CheckSet** marks an error if the item is not a Set.
  end-procedure-description *)
  PROCEDURE CheckSet(VAR x: OXG.Item);
  BEGIN
    IF x.type.form # OXB.Set THEN Mark("not Set"); x.type := OXB.setType END
  END CheckSet;

  (* begin-procedure-description
---
**CheckSetVal** marks an error if the item is not a Set Value.
  end-procedure-description *)
  PROCEDURE CheckSetVal(VAR x: OXG.Item);
  BEGIN
    IF x.type.form # OXB.Int THEN Mark("not Int"); x.type := OXB.setType
    ELSIF x.mode = OXB.Const THEN
      IF (x.a < 0) OR (x.a >= 32) THEN Mark("invalid set") END
    END
  END CheckSetVal;

  (* begin-procedure-description
---
**CheckConst** marks an error if the value is not a Constant.
  end-procedure-description *)
  PROCEDURE CheckConst(VAR x: OXG.Item);
  BEGIN
    IF x.mode # OXB.Const THEN Mark("not a constant"); x.mode := OXB.Const END
  END CheckConst;

  (* begin-procedure-description
---
**CheckReadOnly** marks an error if the value is not read-only.
  end-procedure-description *)
  PROCEDURE CheckReadOnly(VAR x: OXG.Item);
  BEGIN
    IF x.rdo THEN Mark("read-only") END
  END CheckReadOnly;

  (* begin-procedure-description
---
**CheckExport** checks for an export symbol and marks an error if export not at top level.
  end-procedure-description *)
  PROCEDURE CheckExport(VAR expo: BOOLEAN);
  BEGIN
    IF sym = OXS.times THEN
      expo := TRUE; OXS.Get(sym);
      IF level # 0 THEN Mark("remove asterisk") END
    ELSE expo := FALSE
    END
  END CheckExport;

  (* begin-procedure-description
---
**IsExtension** determines if type t1 is an extension of t0.
  end-procedure-description *)
  PROCEDURE IsExtension(t0, t1: OXB.Type): BOOLEAN;
  BEGIN (*t1 is an extension of t0*)
    RETURN (t0 = t1) OR (t1 # NIL) & IsExtension(t0, t1.base)
  END IsExtension;

  (* expressions *)

(* begin-section-description
## ---------- Expressions
  end-section-description *)

  (* begin-procedure-description
---
**TypeTest** checks for assignment type compatibility.
  end-procedure-description *)
  PROCEDURE TypeTest(VAR x: OXG.Item; T: OXB.Type; guard: BOOLEAN);
    VAR xt: OXB.Type;
  BEGIN xt := x.type;
    IF (T.form = xt.form ) & ((T.form = OXB.Pointer) OR (T.form = OXB.Record) & (x.mode = OXB.Par)) THEN
      WHILE (xt # T) & (xt # NIL) DO xt := xt.base END ;
      IF xt # T THEN xt := x.type;
        IF xt.form = OXB.Pointer THEN
          IF IsExtension(xt.base, T.base) THEN OXG.TypeTest(x, T.base, FALSE, guard); x.type := T
          ELSE Mark("not an extension")
          END
        ELSIF (xt.form = OXB.Record) & (x.mode = OXB.Par) THEN
          IF IsExtension(xt, T) THEN  OXG.TypeTest(x, T, TRUE, guard); x.type := T
          ELSE Mark("not an extension")
          END
        ELSE Mark("incompatible types")
        END
      ELSIF ~guard THEN OXG.TypeTest(x, NIL, FALSE, FALSE)
      END
    ELSE Mark("type mismatch")
    END ;
    IF ~guard THEN x.type := OXB.boolType END
  END TypeTest;

  (* begin-procedure-description
---
**selector** generates the array item, procedure, or method dereference on an array or record.
  end-procedure-description *)
  PROCEDURE selector(VAR x: OXG.Item);
    VAR y: OXG.Item; obj: OXB.Object;
  BEGIN
    WHILE (sym = OXS.lbrak) OR (sym = OXS.period) OR (sym = OXS.arrow)
        OR (sym = OXS.lparen) & (x.type.form IN {OXB.Record, OXB.Pointer}) DO
      IF sym = OXS.lbrak THEN
        REPEAT OXS.Get(sym); expression(y);
          IF x.type.form = OXB.Array THEN
            CheckInt(y); OXG.Index(x, y); x.type := x.type.base
          ELSE Mark("not an array")
          END
        UNTIL sym # OXS.comma;
        Check(OXS.rbrak, "no ]")
      ELSIF sym = OXS.period THEN OXS.Get(sym);
        IF sym = OXS.ident THEN
          IF x.type.form = OXB.Pointer THEN OXG.DeRef(x); x.type := x.type.base END ;
          IF x.type.form = OXB.Record THEN
            obj := OXB.thisfield(x.type); OXS.Get(sym);
            IF obj # NIL THEN OXG.Field(x, obj); x.type := obj.type
            ELSE Mark("undef")
            END
          ELSE Mark("not a record")
          END
        ELSE Mark("ident?")
        END
      ELSIF sym = OXS.arrow THEN
        OXS.Get(sym);
        IF x.type.form = OXB.Pointer THEN OXG.DeRef(x); x.type := x.type.base
        ELSE Mark("not a pointer")
        END
      ELSIF (sym = OXS.lparen) & (x.type.form IN {OXB.Record, OXB.Pointer}) THEN (*type guard*)
        OXS.Get(sym);
        IF sym = OXS.ident THEN
          qualident(obj);
          IF obj.class = OXB.Typ THEN TypeTest(x, obj.type, TRUE)
          ELSE Mark("guard type expected")
          END
        ELSE Mark("not an identifier")
        END ;
        Check(OXS.rparen, " ) missing")
      END
    END
  END selector;

  (* begin-procedure-description
---
**EqualSignatures** verifies that a procedure may be assigned to a procedure variable.
  end-procedure-description *)
  PROCEDURE EqualSignatures(t0, t1: OXB.Type): BOOLEAN;
    VAR p0, p1: OXB.Object; com: BOOLEAN;
  BEGIN com := TRUE;
    IF (t0.base = t1.base) & (t0.nofpar = t1.nofpar) THEN
      p0 := t0.dsc; p1 := t1.dsc;
      WHILE p0 # NIL DO
        IF (p0.class = p1.class) &  (p0.rdo = p1.rdo) &
          ((p0.type = p1.type) OR
          (p0.type.form = OXB.Array) & (p1.type.form = OXB.Array) & (p0.type.len = p1.type.len) & (p0.type.base = p1.type.base) OR
          (p0.type.form = OXB.Proc) & (p1.type.form = OXB.Proc) & EqualSignatures(p0.type, p1.type))
        THEN p0 := p0.next; p1 := p1.next
        ELSE p0 := NIL; com := FALSE
        END
      END
    ELSE com := FALSE
    END ;
    RETURN com
  END EqualSignatures;

  (* begin-procedure-description
---
**CompTypes** verifies assigment compatibility by type.
  end-procedure-description *)
  PROCEDURE CompTypes(t0, t1: OXB.Type; varpar: BOOLEAN): BOOLEAN;
  BEGIN (*check for assignment compatibility*)
    RETURN (t0 = t1)    (*openarray assignment disallowed in OXG*)
      OR (t0.form = OXB.Array) & (t1.form = OXB.Array) & (t0.base =  t1.base) & (t0.len = t1.len)
      OR (t0.form = OXB.Record) & (t1.form = OXB.Record)  & IsExtension(t0, t1)
      OR ~varpar &
        ((t0.form = OXB.Pointer) & (t1.form = OXB.Pointer)  & IsExtension(t0.base, t1.base)
        OR (t0.form = OXB.Proc) & (t1.form = OXB.Proc) & EqualSignatures(t0, t1)
        OR (t0.form IN {OXB.Pointer, OXB.Proc}) & (t1.form = OXB.NilTyp))
  END CompTypes;

  (* begin-procedure-description
---
**Parameter** consumes a function call parameter and produces function call proloogue code for the parameter.
  end-procedure-description *)
  PROCEDURE Parameter(par: OXB.Object);
    VAR x: OXG.Item; varpar: BOOLEAN;
  BEGIN expression(x);
    IF par # NIL THEN
      varpar := par.class = OXB.Par;
      IF CompTypes(par.type, x.type, varpar) THEN
        IF ~varpar THEN OXG.ValueParam(x)
        ELSE (*par.class = Par*)
          IF ~par.rdo THEN CheckReadOnly(x) END ;
          OXG.VarParam(x, par.type)
        END
      ELSIF (x.type.form = OXB.Array) & (par.type.form = OXB.Array) &
          (x.type.base = par.type.base) & (par.type.len < 0) THEN
        IF ~par.rdo THEN CheckReadOnly(x) END ;
        OXG.OpenArrayParam(x)
      ELSIF (x.type.form = OXB.String) & varpar & par.rdo & (par.type.form = OXB.Array) &
          (par.type.base.form = OXB.Char) & (par.type.len < 0) THEN OXG.StringParam(x)
      ELSIF ~varpar & (par.type.form = OXB.Int) & (x.type.form = OXB.Int) THEN OXG.ValueParam(x)  (*BYTE*)
      ELSIF (x.type.form = OXB.String) & (x.b = 2) & (par.class = OXB.Var) & (par.type.form = OXB.Char) THEN
        OXG.StrToChar(x); OXG.ValueParam(x)
      ELSIF (par.type.form = OXB.Array) & (par.type.base = OXB.byteType) &
          (par.type.len >= 0) & (par.type.size = x.type.size) THEN
        OXG.VarParam(x, par.type)
      ELSE Mark("incompatible parameters")
      END
    END
  END Parameter;

  (* begin-procedure-description
---
**ParamList** consumes the function call parameters, resulting in a function call prologue.
  end-procedure-description *)
  PROCEDURE ParamList(VAR x: OXG.Item);
    VAR n: INTEGER; par: OXB.Object;
  BEGIN par := x.type.dsc; n := 0;
    IF sym # OXS.rparen THEN
      Parameter(par); n := 1;
      WHILE sym <= OXS.comma DO
        Check(OXS.comma, "comma?");
        IF par # NIL THEN par := par.next END ;
        INC(n); Parameter(par)
      END ;
      Check(OXS.rparen, ") missing")
    ELSE OXS.Get(sym);
    END ;
    IF n < x.type.nofpar THEN Mark("too few params")
    ELSIF n > x.type.nofpar THEN Mark("too many params")
    END
  END ParamList;

  (* begin-procedure-description
---
**StandFunc** consumes standard language functions and produces inline code for those functions.

Standard functions include: ABS ODD FLOOR FLT ORD CHR LEN ADC SBC UML BIT REG VAL ADR SIZE COND H PAU PLY
  end-procedure-description *)
  PROCEDURE StandFunc(VAR x: OXG.Item; fct: INTEGER; restyp: OXB.Type);
    VAR y: OXG.Item; n, npar: INTEGER;
  BEGIN Check(OXS.lparen, "no (");
    npar := fct MOD 10; fct := fct DIV 10; expression(x); n := 1;
    WHILE sym = OXS.comma DO OXS.Get(sym); expression(y); INC(n) END ;
    Check(OXS.rparen, "no )");
    IF n = npar THEN
      IF fct = 0 THEN (*ABS*)
        IF x.type.form IN {OXB.Int, OXB.Real} THEN OXG.Abs(x); restyp := x.type ELSE Mark("bad type") END
      ELSIF fct = 1 THEN (*ODD*) CheckInt(x); OXG.Odd(x)
      ELSIF fct = 2 THEN (*FLOOR*) CheckReal(x); OXG.Floor(x)
      ELSIF fct = 3 THEN (*FLT*) CheckInt(x); OXG.Float(x)
      ELSIF fct = 4 THEN (*ORD*)
        IF x.type.form <= OXB.Proc THEN OXG.Ord(x)
        ELSIF (x.type.form = OXB.String) & (x.b = 2) THEN OXG.StrToChar(x)
        ELSE Mark("bad type")
        END
      ELSIF fct = 5 THEN (*CHR*) CheckInt(x); OXG.Ord(x)
      ELSIF fct = 6 THEN (*LEN*)
          IF x.type.form = OXB.Array THEN OXG.Len(x) ELSE Mark("not an array") END
      ELSIF fct IN {7, 8, 9} THEN (*LSL, ASR, ROR*) CheckInt(y);
        IF x.type.form IN {OXB.Int, OXB.Set} THEN OXG.Shift(fct-7, x, y); restyp := x.type ELSE Mark("bad type") END
      ELSIF fct = 11 THEN (*ADC*) OXG.ADC(x, y)
      ELSIF fct = 12 THEN (*SBC*) OXG.SBC(x, y)
      ELSIF fct = 13 THEN (*UML*) OXG.UML(x, y)
      ELSIF fct = 14 THEN (*BIT*) CheckInt(x); CheckInt(y); OXG.Bit(x, y)
      ELSIF fct = 15 THEN (*REG*) CheckConst(x); CheckInt(x); OXG.Register(x)
      ELSIF fct = 16 THEN (*VAL*)
        IF (x.mode= OXB.Typ) & (x.type.size <= y.type.size) THEN restyp := x.type; x := y
        ELSE Mark("casting not allowed")
        END
      ELSIF fct = 17 THEN (*ADR*) OXG.Adr(x)
      ELSIF fct = 18 THEN (*SIZE*)
        IF x.mode = OXB.Typ THEN OXG.MakeConstItem(x, OXB.intType, x.type.size)
        ELSE Mark("must be a type")
        END
      ELSIF fct = 19 THEN (*COND*) CheckConst(x); CheckInt(x); OXG.Condition(x)
      ELSIF fct = 20 THEN (*H*) CheckConst(x); CheckInt(x); OXG.H(x)
      ELSIF fct = 21 THEN (*PAU*) CheckConst(x); CheckInt(x); OXG.Pau(x)
      ELSIF fct = 22 THEN (*PLY*) CheckConst(x); CheckInt(x); OXG.Ply(x)
      END ;
      x.type := restyp
    ELSE Mark("wrong nof params")
    END
  END StandFunc;

  (* begin-procedure-description
---
**element** produces a reference to an element in a set.
  end-procedure-description *)
  PROCEDURE element(VAR x: OXG.Item);
    VAR y: OXG.Item;
  BEGIN expression(x); CheckSetVal(x);
    IF sym = OXS.upto THEN OXS.Get(sym); expression(y); CheckSetVal(y); OXG.Set(x, y)
    ELSE OXG.Singleton(x)
    END ;
    x.type := OXB.setType
  END element;

  (* begin-procedure-description
---
**set** produces a set from elements.
  end-procedure-description *)
  PROCEDURE set(VAR x: OXG.Item);
    VAR y: OXG.Item;
  BEGIN
    IF sym >= OXS.if THEN
      IF sym # OXS.rbrace THEN Mark(" } missing") END ;
      OXG.MakeConstItem(x, OXB.setType, 0) (*empty set*)
    ELSE element(x);
      WHILE (sym < OXS.rparen) OR (sym > OXS.rbrace) DO
        IF sym = OXS.comma THEN OXS.Get(sym)
        ELSIF sym # OXS.rbrace THEN Mark("missing comma")
        END ;
        element(y); OXG.SetOp(OXS.plus, x, y)
      END
    END
  END set;

  (* begin-procedure-description
---
**factor** generates code that produces a value from identifiers, applications of functions and procedures, etc. for use in a calculation or assignment.
  end-procedure-description *)
  PROCEDURE factor(VAR x: OXG.Item);
    VAR obj: OXB.Object; rx: INTEGER;
  BEGIN (*sync*)
    IF (sym < OXS.char) OR (sym > OXS.ident) THEN Mark("expression expected");
      REPEAT OXS.Get(sym) UNTIL (sym >= OXS.char) & (sym <= OXS.for) OR (sym >= OXS.then)
    END ;
    IF sym = OXS.ident THEN
      qualident(obj);
      IF obj.class = OXB.SFunc THEN StandFunc(x, obj.val, obj.type)
      ELSE OXG.MakeItem(x, obj, level); selector(x);
        IF sym = OXS.lparen THEN
          OXS.Get(sym);
          IF (x.type.form = OXB.Proc) & (x.type.base.form # OXB.NoTyp) THEN
            OXG.PrepCall(x, rx); ParamList(x); OXG.Call(x, rx); x.type := x.type.base
          ELSE Mark("not a function"); ParamList(x)
          END
        END
      END
    ELSIF sym = OXS.int THEN OXG.MakeConstItem(x, OXB.intType, OXS.ival); OXS.Get(sym)
    ELSIF sym = OXS.real THEN OXG.MakeRealItem(x, OXS.rval); OXS.Get(sym)
    ELSIF sym = OXS.char THEN OXG.MakeConstItem(x, OXB.charType, OXS.ival); OXS.Get(sym)
    ELSIF sym = OXS.nil THEN OXS.Get(sym); OXG.MakeConstItem(x, OXB.nilType, 0)
    ELSIF sym = OXS.string THEN OXG.MakeStringItem(x, OXS.slen); OXS.Get(sym)
    ELSIF sym = OXS.lparen THEN OXS.Get(sym); expression(x); Check(OXS.rparen, "no )")
    ELSIF sym = OXS.lbrace THEN OXS.Get(sym); set(x); Check(OXS.rbrace, "no }")
    ELSIF sym = OXS.not THEN OXS.Get(sym); factor(x); CheckBool(x); OXG.Not(x)
    ELSIF sym = OXS.false THEN OXS.Get(sym); OXG.MakeConstItem(x, OXB.boolType, 0)
    ELSIF sym = OXS.true THEN OXS.Get(sym); OXG.MakeConstItem(x, OXB.boolType, 1)
    ELSE Mark("not a factor"); OXG.MakeConstItem(x, OXB.intType, 0)
    END
  END factor;

  (* begin-procedure-description
---
**term** combines factors via multiplication and division, resulting in a value.
  end-procedure-description *)
  PROCEDURE term(VAR x: OXG.Item);
    VAR y: OXG.Item; op, f: INTEGER;
  BEGIN factor(x); f := x.type.form;
    WHILE (sym >= OXS.times) & (sym <= OXS.and) DO
      op := sym; OXS.Get(sym);
      IF op = OXS.times THEN
        IF f = OXB.Int THEN factor(y); CheckInt(y); OXG.MulOp(x, y)
        ELSIF f = OXB.Real THEN factor(y); CheckReal(y); OXG.RealOp(op, x, y)
        ELSIF f = OXB.Set THEN factor(y); CheckSet(y); OXG.SetOp(op, x, y)
        ELSE Mark("bad type")
        END
      ELSIF (op = OXS.div) OR (op = OXS.mod) THEN
        CheckInt(x); factor(y); CheckInt(y); OXG.DivOp(op, x, y)
      ELSIF op = OXS.rdiv THEN
        IF f = OXB.Real THEN factor(y); CheckReal(y); OXG.RealOp(op, x, y)
        ELSIF f = OXB.Set THEN factor(y); CheckSet(y); OXG.SetOp(op, x, y)
        ELSE Mark("bad type")
        END
      ELSE (*op = and*) CheckBool(x); OXG.And1(x); factor(y); CheckBool(y); OXG.And2(x, y)
      END
    END
  END term;

  (* begin-procedure-description
---
**SimpleExpression** combines terms via addition, subtraction, boolean, and set operations, resulting in a value.
  end-procedure-description *)
  PROCEDURE SimpleExpression(VAR x: OXG.Item);
    VAR y: OXG.Item; op: INTEGER;
  BEGIN
    IF sym = OXS.minus THEN OXS.Get(sym); term(x);
      IF x.type.form IN {OXB.Int, OXB.Real, OXB.Set} THEN OXG.Neg(x) ELSE CheckInt(x) END
    ELSIF sym = OXS.plus THEN OXS.Get(sym); term(x);
    ELSE term(x)
    END ;
    WHILE (sym >= OXS.plus) & (sym <= OXS.or) DO
      op := sym; OXS.Get(sym);
      IF op = OXS.or THEN OXG.Or1(x); CheckBool(x); term(y); CheckBool(y); OXG.Or2(x, y)
      ELSIF x.type.form = OXB.Int THEN term(y); CheckInt(y); OXG.AddOp(op, x, y)
      ELSIF x.type.form = OXB.Real THEN term(y); CheckReal(y); OXG.RealOp(op, x, y)
      ELSE CheckSet(x); term(y); CheckSet(y); OXG.SetOp(op, x, y)
      END
    END
  END SimpleExpression;

  (* begin-procedure-description
---
**expression0** produces code handling arbitrary arithmetic and logical operations, resulting in a value.

expression0 is assigned to the procedure variable `expression` to allow the forward reference.

  end-procedure-description *)
  PROCEDURE expression0(VAR x: OXG.Item);
    VAR y: OXG.Item; obj: OXB.Object; rel, xf, yf: INTEGER;
  BEGIN SimpleExpression(x);
    IF (sym >= OXS.eql) & (sym <= OXS.geq) THEN
      rel := sym; OXS.Get(sym); SimpleExpression(y); xf := x.type.form; yf := y.type.form;
      IF x.type = y.type THEN
        IF (xf IN {OXB.Char, OXB.Int}) THEN OXG.IntRelation(rel, x, y)
        ELSIF xf = OXB.Real THEN OXG.RealRelation(rel, x, y)
        ELSIF (xf IN {OXB.Set, OXB.Pointer, OXB.Proc, OXB.NilTyp, OXB.Bool}) THEN
          IF rel <= OXS.neq THEN OXG.IntRelation(rel, x, y) ELSE Mark("only = or #") END
        ELSIF (xf = OXB.Array) & (x.type.base.form = OXB.Char) OR (xf = OXB.String) THEN
          OXG.StringRelation(rel, x, y)
        ELSE Mark("illegal comparison")
        END
      ELSIF (xf IN {OXB.Pointer, OXB.Proc}) & (yf = OXB.NilTyp)
          OR (yf IN {OXB.Pointer, OXB.Proc}) & (xf = OXB.NilTyp) THEN
        IF rel <= OXS.neq THEN OXG.IntRelation(rel, x,  y) ELSE Mark("only = or #") END
      ELSIF (xf = OXB.Pointer) & (yf = OXB.Pointer) &
          (IsExtension(x.type.base, y.type.base) OR IsExtension(y.type.base, x.type.base))
          OR (xf = OXB.Proc) & (yf = OXB.Proc) & EqualSignatures(x.type, y.type) THEN
        IF rel <= OXS.neq THEN OXG.IntRelation(rel,  x, y) ELSE Mark("only = or #") END
      ELSIF (xf = OXB.Array) & (x.type.base.form = OXB.Char) &
            ((yf = OXB.String) OR (yf = OXB.Array) & (y.type.base.form = OXB.Char))
          OR (yf = OXB.Array) & (y.type.base.form = OXB.Char) & (xf = OXB.String) THEN
        OXG.StringRelation(rel, x, y)
      ELSIF (xf = OXB.Char) & (yf = OXB.String) & (y.b = 2) THEN
        OXG.StrToChar(y); OXG.IntRelation(rel, x, y)
      ELSIF (yf = OXB.Char) & (xf = OXB.String) & (x.b = 2) THEN
        OXG.StrToChar(x); OXG.IntRelation(rel, x, y)
      ELSIF (xf = OXB.Int) & (yf = OXB.Int) THEN OXG.IntRelation(rel,  x, y)  (*BYTE*)
      ELSE Mark("illegal comparison")
      END ;
      x.type := OXB.boolType
    ELSIF sym = OXS.in THEN
      OXS.Get(sym); CheckInt(x); SimpleExpression(y); CheckSet(y); OXG.In(x, y) ;
      x.type := OXB.boolType
    ELSIF sym = OXS.is THEN
      OXS.Get(sym); qualident(obj); TypeTest(x, obj.type, FALSE) ;
      x.type := OXB.boolType
    END
  END expression0;

  (* statements *)

(* begin-section-description
## ---------- Statements
  end-section-description *)

  (* begin-procedure-description
---
**StandProc** handles standard (predefined) procedures.
  end-procedure-description *)
  PROCEDURE StandProc(pno: INTEGER);
    VAR nap, npar: INTEGER; (*nof actual/formal parameters*)
      x, y, z: OXG.Item;
  BEGIN Check(OXS.lparen, "no (");
    npar := pno MOD 10; pno := pno DIV 10; expression(x); nap := 1;
    IF sym = OXS.comma THEN
      OXS.Get(sym); expression(y); nap := 2; z.type := OXB.noType;
      WHILE sym = OXS.comma DO OXS.Get(sym); expression(z); INC(nap) END
    ELSE y.type := OXB.noType
    END ;
    Check(OXS.rparen, "no )");
    IF (npar = nap) OR (pno IN {0, 1}) THEN
      IF pno IN {0, 1} THEN (*INC, DEC*)
        CheckInt(x); CheckReadOnly(x);
        IF y.type # OXB.noType THEN CheckInt(y) END ;
        OXG.Increment(pno, x, y)
      ELSIF pno IN {2, 3} THEN (*INCL, EXCL*)
        CheckSet(x); CheckReadOnly(x); CheckInt(y); OXG.Include(pno-2, x, y)
      ELSIF pno = 4 THEN CheckBool(x); OXG.Assert(x)
      ELSIF pno = 5 THEN(*NEW*) CheckReadOnly(x);
         IF (x.type.form = OXB.Pointer) & (x.type.base.form = OXB.Record) THEN OXG.New(x)
         ELSE Mark("not a pointer to record")
         END
      ELSIF pno = 6 THEN CheckReal(x); CheckInt(y); CheckReadOnly(x); OXG.Pack(x, y)
      ELSIF pno = 7 THEN CheckReal(x); CheckInt(y); CheckReadOnly(x); OXG.Unpk(x, y)
      ELSIF pno = 8 THEN
        IF x.type.form <= OXB.Set THEN OXG.Led(x) ELSE Mark("bad type") END
      ELSIF pno = 9 THEN
        IF x.type.form <= OXB.Set THEN OXG.Ouch(x) ELSE Mark("bad type") END
      ELSIF pno = 10 THEN CheckInt(x); OXG.Get(x, y)
      ELSIF pno = 11 THEN CheckInt(x); OXG.Put(x, y)
      ELSIF pno = 12 THEN CheckInt(x); CheckInt(y); CheckInt(z); OXG.Copy(x, y, z)
      ELSIF pno = 13 THEN CheckConst(x); CheckInt(x); OXG.LDPSR(x)
      ELSIF pno = 14 THEN CheckInt(x); OXG.LDREG(x, y)
      ELSIF pno = 21 THEN CheckInt(x); CheckInt(y); OXG.REGREG(x, y)
      END
    ELSE Mark("wrong nof parameters")
    END
  END StandProc;

  (* begin-procedure-description
---
**StatSequence** matches a statement sequence.
  end-procedure-description *)
  PROCEDURE StatSequence;
    VAR obj: OXB.Object;
      orgtype: OXB.Type; (*original type of case var*)
      x, y, z, w: OXG.Item;
      L0, L1, rx: INTEGER;

  (* begin-procedure-description
**TypeCase** (interior procedure)
  end-procedure-description *)
    PROCEDURE TypeCase(obj: OXB.Object; VAR x: OXG.Item);
      VAR typobj: OXB.Object;
    BEGIN
      IF sym = OXS.ident THEN
        qualident(typobj); OXG.MakeItem(x, obj, level);
        IF typobj.class # OXB.Typ THEN Mark("not a type") END ;
        TypeTest(x, typobj.type, FALSE); obj.type := typobj.type;
        OXG.CFJump(x); Check(OXS.colon, ": expected"); StatSequence
      ELSE OXG.CFJump(x); Mark("type id expected")
      END
     END TypeCase;

  (* begin-procedure-description
**SkipCase** (interior procedure)
  end-procedure-description *)
    PROCEDURE SkipCase;
    BEGIN
      WHILE sym # OXS.colon DO OXS.Get(sym) END ;
      OXS.Get(sym); StatSequence
    END SkipCase;

  BEGIN (* StatSequence *)
    REPEAT (*sync*) obj := NIL;
      IF ~((sym >= OXS.ident)  & (sym <= OXS.for) OR (sym >= OXS.semicolon)) THEN
        Mark("statement expected");
        REPEAT OXS.Get(sym) UNTIL (sym >= OXS.ident)
      END ;
      IF sym = OXS.ident THEN
        qualident(obj); OXG.MakeItem(x, obj, level);
        IF x.mode = OXB.SProc THEN StandProc(obj.val)
        ELSE selector(x);
          IF sym = OXS.becomes THEN (*assignment*)
            OXS.Get(sym); CheckReadOnly(x); expression(y);
            IF CompTypes(x.type, y.type, FALSE) THEN
              IF (x.type.form <= OXB.Pointer) OR (x.type.form = OXB.Proc) THEN OXG.Store(x, y)
              ELSE OXG.StoreStruct(x, y)
              END
            ELSIF (x.type.form = OXB.Array) & (y.type.form = OXB.Array) & (x.type.base = y.type.base) & (y.type.len < 0) THEN
              OXG.StoreStruct(x, y)
            ELSIF (x.type.form = OXB.Array) & (x.type.base.form = OXB.Char) & (y.type.form = OXB.String) THEN
              OXG.CopyString(x, y)
            ELSIF (x.type.form = OXB.Int) & (y.type.form = OXB.Int) THEN OXG.Store(x, y)  (*BYTE*)
            ELSIF (x.type.form = OXB.Char) & (y.type.form = OXB.String) & (y.b = 2) THEN
              OXG.StrToChar(y); OXG.Store(x, y)
            ELSE Mark("illegal assignment")
            END
          ELSIF sym = OXS.eql THEN Mark("should be :="); OXS.Get(sym); expression(y)
          ELSIF sym = OXS.lparen THEN (*procedure call*)
            OXS.Get(sym);
            IF (x.type.form = OXB.Proc) & (x.type.base.form = OXB.NoTyp) THEN
              OXG.PrepCall(x, rx); ParamList(x); OXG.Call(x, rx)
            ELSE Mark("not a procedure"); ParamList(x)
            END
          ELSIF x.type.form = OXB.Proc THEN (*procedure call without parameters*)
            IF x.type.nofpar > 0 THEN Mark("missing parameters") END ;
            IF x.type.base.form = OXB.NoTyp THEN OXG.PrepCall(x, rx); OXG.Call(x, rx) ELSE Mark("not a procedure") END
          ELSIF x.mode = OXB.Typ THEN Mark("illegal assignment")
          ELSE Mark("not a procedure")
          END
        END
      ELSIF sym = OXS.if THEN
        OXS.Get(sym); expression(x); CheckBool(x); OXG.CFJump(x);
        Check(OXS.then, "no THEN");
        StatSequence; L0 := 0;
        WHILE sym = OXS.elsif DO
          OXS.Get(sym); OXG.FJump(L0); OXG.Fixup(x); expression(x); CheckBool(x);
          OXG.CFJump(x); Check(OXS.then, "no THEN"); StatSequence
        END ;
        IF sym = OXS.else THEN OXS.Get(sym); OXG.FJump(L0); OXG.Fixup(x); StatSequence
        ELSE OXG.Fixup(x)
        END ;
        OXG.FixLink(L0); Check(OXS.end, "no END")
      ELSIF sym = OXS.while THEN
        OXS.Get(sym); L0 := OXG.Here(); expression(x); CheckBool(x); OXG.CFJump(x);
        Check(OXS.do, "no DO"); StatSequence; OXG.BJump(L0);
        WHILE sym = OXS.elsif DO
          OXS.Get(sym); OXG.Fixup(x); expression(x); CheckBool(x); OXG.CFJump(x);
          Check(OXS.do, "no DO"); StatSequence; OXG.BJump(L0)
        END ;
        OXG.Fixup(x); Check(OXS.end, "no END")
      ELSIF sym = OXS.repeat THEN
        OXS.Get(sym); L0 := OXG.Here(); StatSequence;
        IF sym = OXS.until THEN
          OXS.Get(sym); expression(x); CheckBool(x); OXG.CBJump(x, L0)
        ELSE Mark("missing UNTIL")
        END
      ELSIF sym = OXS.for THEN
        OXS.Get(sym);
        IF sym = OXS.ident THEN
          qualident(obj); OXG.MakeItem(x, obj, level); CheckInt(x); CheckReadOnly(x);
          IF sym = OXS.becomes THEN
            OXS.Get(sym); expression(y); CheckInt(y); OXG.For0(x, y); L0 := OXG.Here();
            Check(OXS.to, "no TO"); expression(z); CheckInt(z); obj.rdo := TRUE;
            IF sym = OXS.by THEN OXS.Get(sym); expression(w); CheckConst(w); CheckInt(w)
            ELSE OXG.MakeConstItem(w, OXB.intType, 1)
            END ;
            Check(OXS.do, "no DO"); OXG.For1(x, y, z, w, L1);
            StatSequence; Check(OXS.end, "no END");
            OXG.For2(x, y, w); OXG.BJump(L0); OXG.FixLink(L1); obj.rdo := FALSE
          ELSE Mark(":= expected")
          END
        ELSE Mark("identifier expected")
        END
      ELSIF sym = OXS.case THEN
        OXS.Get(sym);
        IF sym = OXS.ident THEN
          qualident(obj); orgtype := obj.type;
          IF (orgtype.form = OXB.Pointer) OR (orgtype.form = OXB.Record) & (obj.class = OXB.Par) THEN
            Check(OXS.of, "OF expected"); TypeCase(obj, x); L0 := 0;
            WHILE sym = OXS.bar DO
              OXS.Get(sym); OXG.FJump(L0); OXG.Fixup(x); obj.type := orgtype; TypeCase(obj, x)
            END ;
            OXG.Fixup(x); OXG.FixLink(L0); obj.type := orgtype
          ELSE Mark("numeric case not implemented");
            Check(OXS.of, "OF expected"); SkipCase;
            WHILE sym = OXS.bar DO SkipCase END
          END
        ELSE Mark("ident expected")
        END ;
        Check(OXS.end, "no END")
      END ;
      OXG.CheckRegs;
      IF sym = OXS.semicolon THEN OXS.Get(sym)
      ELSIF sym < OXS.semicolon THEN Mark("missing semicolon?")
      END
    UNTIL sym > OXS.semicolon
  END StatSequence;

  (* Types and declarations *)

(* begin-section-description
## ---------- Types and declarations
  end-section-description *)

  (* begin-procedure-description
---
**IdentList** matches a comma separated list of identifiers.
  end-procedure-description *)
  PROCEDURE IdentList(class: INTEGER; VAR first: OXB.Object);
    VAR obj: OXB.Object;
  BEGIN
    IF sym = OXS.ident THEN
      OXB.NewObj(first, OXS.id, class); OXS.Get(sym); CheckExport(first.expo);
      WHILE sym = OXS.comma DO
        OXS.Get(sym);
        IF sym = OXS.ident THEN OXB.NewObj(obj, OXS.id, class); OXS.Get(sym); CheckExport(obj.expo)
        ELSE Mark("ident?")
        END
      END;
      IF sym = OXS.colon THEN OXS.Get(sym) ELSE Mark(":?") END
    ELSE first := NIL
    END
  END IdentList;

  (* begin-procedure-description
---
**ArrayType** matches the definiton of an Array Type or marks an error.
  end-procedure-description *)
  PROCEDURE ArrayType(VAR type: OXB.Type);
    VAR x: OXG.Item; typ: OXB.Type; len: INTEGER;
  BEGIN NEW(typ); typ.form := OXB.NoTyp;
    expression(x);
    IF (x.mode = OXB.Const) & (x.type.form = OXB.Int) & (x.a >= 0) THEN len := x.a
    ELSE len := 1; Mark("not a valid length")
    END ;
    IF sym = OXS.of THEN OXS.Get(sym); Type(typ.base);
      IF (typ.base.form = OXB.Array) & (typ.base.len < 0) THEN Mark("dyn array not allowed") END
    ELSIF sym = OXS.comma THEN OXS.Get(sym); ArrayType(typ.base)
    ELSE Mark("missing OF"); typ.base := OXB.intType
    END ;
    typ.size := (len * typ.base.size + 3) DIV 4 * 4;
    typ.form := OXB.Array; typ.len := len; type := typ
  END ArrayType;

  (* begin-procedure-description
---
**RecordType** matches the definition of a Record Type or marks an error.
  end-procedure-description *)
  PROCEDURE RecordType(VAR type: OXB.Type);
    VAR obj, obj0, new, bot, base: OXB.Object;
      typ, tp: OXB.Type;
      offset, off, n: INTEGER;
  BEGIN NEW(typ); typ.form := OXB.NoTyp; typ.base := NIL; typ.mno := -level; typ.nofpar := 0; offset := 0; bot := NIL;
    IF sym = OXS.lparen THEN
      OXS.Get(sym); (*record extension*)
      IF level # 0 THEN Mark("extension of local types not implemented") END ;
      IF sym = OXS.ident THEN
        qualident(base);
        IF base.class = OXB.Typ THEN
          IF base.type.form = OXB.Record THEN typ.base := base.type
          ELSE typ.base := OXB.intType; Mark("invalid extension")
          END ;
          typ.nofpar := typ.base.nofpar + 1; (*"nofpar" here abused for extension level*)
          bot := typ.base.dsc; offset := typ.base.size
        ELSE Mark("type expected")
        END
      ELSE Mark("ident expected")
      END ;
      Check(OXS.rparen, "no )")
    END ;
    WHILE sym = OXS.ident DO  (*fields*)
      n := 0; obj := bot;
      WHILE sym = OXS.ident DO
        obj0 := obj;
        WHILE (obj0 # NIL) & (obj0.name # OXS.id) DO obj0 := obj0.next END ;
        IF obj0 # NIL THEN Mark("mult def") END ;
        NEW(new); OXS.CopyId(new.name); new.class := OXB.Fld; new.next := obj; obj := new; INC(n);
        OXS.Get(sym); CheckExport(new.expo);
        IF (sym # OXS.comma) & (sym # OXS.colon) THEN Mark("comma expected")
        ELSIF sym = OXS.comma THEN OXS.Get(sym)
        END
      END ;
      Check(OXS.colon, "colon expected"); Type(tp);
      IF (tp.form = OXB.Array) & (tp.len < 0) THEN Mark("dyn array not allowed") END ;
      IF tp.size > 1 THEN offset := (offset+3) DIV 4 * 4 END ;
      offset := offset + n * tp.size; off := offset; obj0 := obj;
      WHILE obj0 # bot DO obj0.type := tp; obj0.lev := 0; off := off - tp.size; obj0.val := off; obj0 := obj0.next END ;
      bot := obj;
      IF sym = OXS.semicolon THEN OXS.Get(sym) ELSIF sym # OXS.end THEN Mark(" ; or END") END
    END ;
    typ.form := OXB.Record; typ.dsc := bot; typ.size := (offset + 3) DIV 4 * 4; type := typ
  END RecordType;

  (* begin-procedure-description
---
**FPSection** matches the parameters to a function or marks an error.
  end-procedure-description *)
  PROCEDURE FPSection(VAR adr: INTEGER; VAR nofpar: INTEGER);
    VAR obj, first: OXB.Object; tp: OXB.Type;
      parsize: INTEGER; cl: INTEGER; rdo: BOOLEAN;
  BEGIN
    IF sym = OXS.var THEN OXS.Get(sym); cl := OXB.Par ELSE cl := OXB.Var END ;
    IdentList(cl, first); FormalType(tp, 0); rdo := FALSE;
    IF (cl = OXB.Var) & (tp.form >= OXB.Array) THEN cl := OXB.Par; rdo := TRUE END ;
    IF (tp.form = OXB.Array) & (tp.len < 0) OR (tp.form = OXB.Record) THEN
      parsize := 2*ccWordsize  (*open array or record, needs second word for length or type tag*)
    ELSE parsize := ccWordsize
    END ;
    obj := first;
    WHILE obj # NIL DO
      INC(nofpar); obj.class := cl; obj.type := tp; obj.rdo := rdo; obj.lev := level; obj.val := adr;
      adr := adr + parsize; obj := obj.next
    END ;
    IF adr >= 52 THEN Mark("too many parameters") END
  END FPSection;

  (* begin-procedure-description
---
**ProcedureType** matches a Procedure Type definition or marks an error.
  end-procedure-description *)
  PROCEDURE ProcedureType(ptype: OXB.Type; VAR parblksize: INTEGER);
    VAR obj: OXB.Object; size: INTEGER; nofpar: INTEGER;
  BEGIN ptype.base := OXB.noType; size := parblksize; nofpar := 0; ptype.dsc := NIL;
    IF sym = OXS.lparen THEN
      OXS.Get(sym);
      IF sym = OXS.rparen THEN OXS.Get(sym)
      ELSE FPSection(size, nofpar);
        WHILE sym = OXS.semicolon DO OXS.Get(sym); FPSection(size, nofpar) END ;
        Check(OXS.rparen, "no )")
      END ;
      IF sym = OXS.colon THEN  (*function*)
        OXS.Get(sym);
        IF sym = OXS.ident THEN
          qualident(obj); ptype.base := obj.type;
          IF ~((obj.class = OXB.Typ) & (obj.type.form IN {OXB.Byte .. OXB.Pointer, OXB.Proc})) THEN
            Mark("illegal function type")
          END
        ELSE Mark("type identifier expected")
        END
      END
    END ;
    ptype.nofpar := nofpar; parblksize := size
  END ProcedureType;

  (* begin-procedure-description
---
**FormalType0** matches the definition of a type or marks an error.
  end-procedure-description *)
  PROCEDURE FormalType0(VAR typ: OXB.Type; dim: INTEGER);
    VAR obj: OXB.Object; dmy: INTEGER;
  BEGIN
    IF sym = OXS.ident THEN
      qualident(obj);
      IF obj.class = OXB.Typ THEN typ := obj.type ELSE Mark("not a type"); typ := OXB.intType END
    ELSIF sym = OXS.array THEN
      OXS.Get(sym); Check(OXS.of, "OF ?");
      IF dim >= 1 THEN Mark("multi-dimensional open arrays not implemented") END ;
      NEW(typ); typ.form := OXB.Array; typ.len := -1; typ.size := 2*ccWordsize;
      FormalType(typ.base, dim+1)
    ELSIF sym = OXS.procedure THEN
      OXS.Get(sym); OXB.OpenScope;
      NEW(typ); typ.form := OXB.Proc; typ.size := ccWordsize; dmy := 0; ProcedureType(typ, dmy);
      typ.dsc := OXB.topScope.next; OXB.CloseScope
    ELSE Mark("identifier expected"); typ := OXB.noType
    END
  END FormalType0;

  (* begin-procedure-description
---
**CheckRecLevel** ensures that the ptr base is global.
  end-procedure-description *)
  PROCEDURE CheckRecLevel(lev: INTEGER);
  BEGIN
    IF lev # 0 THEN Mark("ptr base must be global") END
  END CheckRecLevel;

  (* begin-procedure-description
---
**Type0** matches a type definition or marks an error.
  end-procedure-description *)
  PROCEDURE Type0(VAR type: OXB.Type);
    VAR dmy: INTEGER; obj: OXB.Object; ptbase: PtrBase;
  BEGIN type := OXB.intType; (*sync*)
    IF (sym # OXS.ident) & (sym < OXS.array) THEN Mark("not a type");
      REPEAT OXS.Get(sym) UNTIL (sym = OXS.ident) OR (sym >= OXS.array)
    END ;
    IF sym = OXS.ident THEN
      qualident(obj);
      IF obj.class = OXB.Typ THEN
        IF (obj.type # NIL) & (obj.type.form # OXB.NoTyp) THEN type := obj.type END
      ELSE Mark("not a type or undefined")
      END
    ELSIF sym = OXS.array THEN OXS.Get(sym); ArrayType(type)
    ELSIF sym = OXS.record THEN
      OXS.Get(sym); RecordType(type); Check(OXS.end, "no END")
    ELSIF sym = OXS.pointer THEN
      OXS.Get(sym); Check(OXS.to, "no TO");
      NEW(type);  type.form := OXB.Pointer; type.size := ccWordsize; type.base := OXB.intType;
      IF sym = OXS.ident THEN
        obj := OXB.thisObj();
        IF obj # NIL THEN
          IF (obj.class = OXB.Typ) & (obj.type.form IN {OXB.Record, OXB.NoTyp}) THEN
            CheckRecLevel(obj.lev); type.base := obj.type
          ELSIF obj.class = OXB.Mod THEN Mark("external base type not implemented")
          ELSE Mark("no valid base type")
          END
        ELSE CheckRecLevel(level); (*enter into list of forward references to be fixed in Declarations*)
          NEW(ptbase); OXS.CopyId(ptbase.name); ptbase.type := type; ptbase.next := pbsList; pbsList := ptbase
        END ;
        OXS.Get(sym)
      ELSE Type(type.base);
        IF (type.base.form # OXB.Record) OR (type.base.typobj = NIL) THEN Mark("must point to named record") END ;
        CheckRecLevel(level)
      END
    ELSIF sym = OXS.procedure THEN
      OXS.Get(sym); OXB.OpenScope;
      NEW(type); type.form := OXB.Proc; type.size := ccWordsize; dmy := 0;
      ProcedureType(type, dmy); type.dsc := OXB.topScope.next; OXB.CloseScope
    ELSE Mark("illegal type")
    END
  END Type0;

  (* begin-procedure-description
---
**Declarations** dispatches the definition of constants, types, and variables.
  end-procedure-description *)
  PROCEDURE Declarations(VAR varsize: INTEGER);
    VAR obj, first: OXB.Object;
      x: OXG.Item; tp: OXB.Type; ptbase: PtrBase;
      expo: BOOLEAN; id: OXS.Ident;
  BEGIN (*sync*) pbsList := NIL;
    IF (sym < OXS.const) & (sym # OXS.end) & (sym # OXS.return) THEN Mark("declaration?");
      REPEAT OXS.Get(sym) UNTIL (sym >= OXS.const) OR (sym = OXS.end) OR (sym = OXS.return)
    END ;
    IF sym = OXS.const THEN
      OXS.Get(sym);
      WHILE sym = OXS.ident DO
        OXS.CopyId(id); OXS.Get(sym); CheckExport(expo);
        IF sym = OXS.eql THEN OXS.Get(sym) ELSE Mark("= ?") END;
        expression(x);
        IF (x.type.form = OXB.String) & (x.b = 2) THEN OXG.StrToChar(x) END ;
        OXB.NewObj(obj, id, OXB.Const); obj.expo := expo;
        IF x.mode = OXB.Const THEN obj.val := x.a; obj.lev := x.b; obj.type := x.type
        ELSE Mark("expression not constant"); obj.type := OXB.intType
        END;
        Check(OXS.semicolon, "; missing")
      END
    END ;
    IF sym = OXS.type THEN
      OXS.Get(sym);
      WHILE sym = OXS.ident DO
        OXS.CopyId(id); OXS.Get(sym); CheckExport(expo);
        IF sym = OXS.eql THEN OXS.Get(sym) ELSE Mark("=?") END ;
        Type(tp);
        OXB.NewObj(obj, id, OXB.Typ); obj.type := tp; obj.expo := expo; obj.lev := level;
        IF tp.typobj = NIL THEN tp.typobj := obj END ;
        IF expo & (obj.type.form = OXB.Record) THEN obj.exno := exno; INC(exno) ELSE obj.exno := 0 END ;
        IF tp.form = OXB.Record THEN
          ptbase := pbsList;  (*check whether this is base of a pointer type; search and fixup*)
          WHILE ptbase # NIL DO
            IF obj.name = ptbase.name THEN ptbase.type.base := obj.type END ;
            ptbase := ptbase.next
          END ;
          IF level = 0 THEN OXG.BuildTD(tp, dc) END    (*type descriptor; len used as its address*)
        END ;
        Check(OXS.semicolon, "; missing")
      END
    END ;
    IF sym = OXS.var THEN
      OXS.Get(sym);
      WHILE sym = OXS.ident DO
        IdentList(OXB.Var, first); Type(tp);
        obj := first;
        WHILE obj # NIL DO
          obj.type := tp; obj.lev := level;
          IF tp.size > 1 THEN varsize := (varsize + 3) DIV 4 * 4 (*align*) END ;
          obj.val := varsize; varsize := varsize + obj.type.size;
          IF obj.expo THEN obj.exno := exno; INC(exno) END ;
          obj := obj.next
        END ;
        Check(OXS.semicolon, "; missing")
      END
    END ;
    varsize := (varsize + ccStackalign - 1) DIV ccStackalign * ccStackalign;
(*    varsize := (varsize + 3) DIV 4 * 4; *)
    ptbase := pbsList;
    WHILE ptbase # NIL DO
      IF ptbase.type.base.form = OXB.Int THEN Mark("undefined pointer base of") END ;
      ptbase := ptbase.next
    END ;
    IF (sym >= OXS.const) & (sym <= OXS.var) THEN Mark("declaration in bad order") END
  END Declarations;

  (* begin-procedure-description
---
**ProcedureDecl** matches the definition of a procedure or marks an error.
  end-procedure-description *)
  PROCEDURE ProcedureDecl;
    VAR proc: OXB.Object;
      type: OXB.Type;
      procid: OXS.Ident;
      x: OXG.Item;
      locblksize, parblksize, L: INTEGER;
      int: BOOLEAN;
  BEGIN (* ProcedureDecl *) int := FALSE; OXS.Get(sym);
    IF sym = OXS.times THEN OXS.Get(sym); int := TRUE END ;
    IF sym = OXS.ident THEN
      OXS.CopyId(procid); OXS.Get(sym);
      OXB.NewObj(proc, OXS.id, OXB.Const);
      IF int THEN parblksize := 3 * ccWordsize ELSE parblksize := ccWordsize END ;
      NEW(type); type.form := OXB.Proc; type.size := ccWordsize;
      proc.type := type; proc.val := -1; proc.lev := level;
      CheckExport(proc.expo);
      IF proc.expo THEN proc.exno := exno; INC(exno) END ;
      OXB.OpenScope; INC(level); type.base := OXB.noType;
      ProcedureType(type, parblksize);  (*formal parameter list*)
      Check(OXS.semicolon, "no ;"); locblksize := parblksize;
      Declarations(locblksize);
      proc.val := OXG.Here() * 4; proc.type.dsc := OXB.topScope.next;
      IF sym = OXS.procedure THEN
        L := 0; OXG.FJump(L);
        REPEAT ProcedureDecl; Check(OXS.semicolon, "no ;") UNTIL sym # OXS.procedure;
        OXG.FixOne(L); proc.val := OXG.Here() * 4; proc.type.dsc := OXB.topScope.next
      END ;
      OXG.Enter(parblksize, locblksize, ccWordsize, int);
(*      proc.val2:=locblksize; *)
      IF sym = OXS.begin THEN OXS.Get(sym); StatSequence END ;
      IF sym = OXS.return THEN
        OXS.Get(sym); expression(x);
        IF type.base = OXB.noType THEN Mark("this is not a function")
        ELSIF ~CompTypes(type.base, x.type, FALSE) THEN Mark("wrong result type")
        END
      ELSIF type.base.form # OXB.NoTyp THEN
        Mark("function without result"); type.base := OXB.noType
      END ;
      OXG.Return(type.base.form, x, locblksize, int);
      OXB.CloseScope; DEC(level); Check(OXS.end, "no END");
      IF sym = OXS.ident THEN
        IF OXS.id # procid THEN Mark("no match") END ;
        OXS.Get(sym)
      ELSE Mark("no proc id")
      END
    ELSE Mark("proc id expected")
    END
  END ProcedureDecl;

  (* begin-procedure-description
---
**Import** consumes the names of modules imported by this module and ensures their compatibility or marks an error.
  end-procedure-description *)
  PROCEDURE Import;
    VAR impid, impid1: OXS.Ident;
  BEGIN
    IF sym = OXS.ident THEN
      OXS.CopyId(impid); OXS.Get(sym);
      IF sym = OXS.becomes THEN
        OXS.Get(sym);
        IF sym = OXS.ident THEN OXS.CopyId(impid1); OXS.Get(sym)
        ELSE Mark("id expected"); impid1 := impid
        END
      ELSE impid1 := impid
      END ;
      OXB.Import(impid, impid1, ccARCH)
    ELSE Mark("id expected")
    END
  END Import;

  (* begin-procedure-description
---
**Module** begins the recursive descent parsing of the source text and emits an object code file on completion or marks an error.
  end-procedure-description *)
  PROCEDURE Module;
    VAR key: INTEGER;
  BEGIN OXS.Get(sym);
    IF OXS.ccARCH = OXS.RISC5 THEN Emit( " for RISC5 ") END;
    IF OXS.ccARCH = OXS.X8664 THEN Emit( " for X8664 ") END;
    IF OXS.ccARCH = OXS.ARM64 THEN Emit( " for ARM64 ") END;
    IF OXS.ccARCH = OXS.ARM32 THEN Emit( " for ARM32 ") END;
    IF OXS.ccARCH = OXS.RISCV64 THEN Emit( " for RISCV64 ") END;
    IF OXS.ccARCH = OXS.RISCV32 THEN Emit( " for RISCV32 ") END;
    IF sym = OXS.module THEN
      OXS.Get(sym);
      IF sym = OXS.times THEN version := 0; dc := 8; Emit( "*"); OXS.Get(sym) ELSE dc := 0; version := 1 END ;
      OXB.Clear; OXB.OpenScope;
      IF sym = OXS.ident THEN
        OXS.CopyId(modid); OXS.Get(sym);
        Emit( modid);
      ELSE Mark("identifier expected")
      END ;
      Check(OXS.semicolon, "no ;"); level := 0; exno := 1; key := 0;
      IF sym = OXS.import THEN
        OXS.Get(sym); Import;
        WHILE sym = OXS.comma DO OXS.Get(sym); Import END ;
        Check(OXS.semicolon, "; missing")
      END ;
      OXG.Open(version); Declarations(dc); OXG.SetDataSize((dc + 3) DIV 4 * 4);
      WHILE sym = OXS.procedure DO ProcedureDecl; Check(OXS.semicolon, "no ;") END ;
      OXG.Header;
      IF sym = OXS.begin THEN OXS.Get(sym); StatSequence END ;
      Check(OXS.end, "no END");
      IF sym = OXS.ident THEN
        IF OXS.id # modid THEN Mark("no match") END ;
        OXS.Get(sym)
      ELSE Mark("identifier missing")
      END ;
      IF sym # OXS.period THEN Mark("period missing") END ;
      IF (OXS.errcnt = 0) & (version # 0) THEN
        OXB.Export(modid, newSF, key, ccARCH);
        IF newSF THEN Emit(" new symbol file") END
      END ;
      Out.Ln;
      IF OXS.errcnt = 0 THEN
        OXG.Close(modid, key, exno, ccARCH);
        Emit(" PC, DC, Key: "); Out.Int(OXG.pc, 6); Out.Int( dc, 6); Out.Hex(key)
      ELSE Out.Ln; Emit("compilation FAILED")
      END ;
      Out.Ln; 
      OXB.CloseScope; pbsList := NIL
    ELSE Mark("must start with MODULE")
    END
  END Module;

(* begin-section-description
## ---------- Command Invocation
  end-section-description *)

  (* begin-procedure-description
---
**Option** checks if a new symbol file may be generated and which architecture to compile for.
  end-procedure-description *)
  PROCEDURE Option(o: Options);
    VAR i: INTEGER;
  BEGIN newSF := FALSE;
    ccARCH := OXS.RISC5;
    ccWordsize := 4;
    ccStackalign := 4;
    i:=0; WHILE o[i] > 0X DO
      IF o[i] = "s" THEN newSF := TRUE END;
      IF o[i] = "r" THEN ccARCH := OXS.RISC5 END;
      IF o[i] = "R" THEN ccARCH := OXS.ERISC5 END;
      IF o[i] = "I" THEN ccARCH := OXS.X8664; ccWordsize := 8; ccStackalign := 8; END;
      IF o[i] = "A" THEN ccARCH := OXS.ARM64; ccWordsize := 8; ccStackalign := 16; END;
      IF o[i] = "a" THEN ccARCH := OXS.ARM32 END;
      IF o[i] = "C" THEN ccARCH := OXS.CORTEX4 END;
      IF o[i] = "c" THEN ccARCH := OXS.CORTEX0 END;
      IF o[i] = "V" THEN ccARCH := OXS.RISCV64; ccWordsize := 8; ccStackalign := 8; END;
      IF o[i] = "v" THEN ccARCH := OXS.RISCV32 END;
      IF o[i] = "W" THEN ccARCH := OXS.WASM; ccWordsize := 8; ccStackalign := 8; END;
      INC(i)
    END
  END Option;


  (* begin-procedure-description
---
**Prep** locates the source code to a module, initializes the scanner, and begins parsing at 'Module'.
  end-procedure-description *)
  PROCEDURE Prep;
    VAR ss: OXS.Ident;
  BEGIN
    OXB.Init(ccWordsize);

    (*initialize universe with data types and in-line procedures;
      INTEGER and INTEGER are register size in 32 and 64 bit systems.
      REAL and LONGREAL resgister size in 32 and 64 bit systems.
      LED, ADC, SBC; LDPSR, LDREG, REG, COND are not in language definition*)

    ss:="UML";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 132);  (*functions*)
    ss:="SBC";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 122);
    ss:="ADC";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 112);
    ss:="ROR";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 92);
    ss:="ASR";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 82);
    ss:="LSL";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 72);
    ss:="LEN";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 61);
    ss:="CHR";    OXB.Enter( ss,    OXB.SFunc, OXB.charType, 51);
    ss:="ORD";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 41);
    ss:="FLT";    OXB.Enter( ss,    OXB.SFunc, OXB.realType, 31);
    ss:="FLOOR";  OXB.Enter( ss,    OXB.SFunc, OXB.intType, 21);
    ss:="ODD";    OXB.Enter( ss,    OXB.SFunc, OXB.boolType, 11);
    ss:="ABS";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 1);
    ss:="PAU";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 211);
    ss:="PLY";    OXB.Enter( ss,    OXB.SFunc, OXB.intType, 221);
    ss:="OUCH";   OXB.Enter( ss,    OXB.SProc, OXB.noType, 91);  (*procedures*)
    ss:="LED";    OXB.Enter( ss,    OXB.SProc, OXB.noType, 81);
    ss:="UNPK";   OXB.Enter( ss,    OXB.SProc, OXB.noType, 72);
    ss:="PACK";   OXB.Enter( ss,    OXB.SProc, OXB.noType, 62);
    ss:="NEW";    OXB.Enter( ss,    OXB.SProc, OXB.noType, 51);
    ss:="ASSERT"; OXB.Enter( ss,    OXB.SProc, OXB.noType, 41);
    ss:="EXCL";   OXB.Enter( ss,    OXB.SProc, OXB.noType, 32);
    ss:="INCL";   OXB.Enter( ss,    OXB.SProc, OXB.noType, 22);
    ss:="DEC";    OXB.Enter( ss,    OXB.SProc, OXB.noType, 11);
    ss:="INC";    OXB.Enter( ss,    OXB.SProc, OXB.noType, 1);
    ss:="SET";    OXB.Enter( ss,    OXB.Typ,   OXB.setType, 0);   (*types*)
    ss:="BOOLEAN";OXB.Enter( ss,    OXB.Typ,   OXB.boolType, 0);
    ss:="BYTE";   OXB.Enter( ss,    OXB.Typ,   OXB.byteType, 0);
    ss:="CHAR";   OXB.Enter( ss,    OXB.Typ,   OXB.charType, 0);
    IF ccWordsize = 4 THEN ss:="LONGREAL"; OXB.Enter( ss, OXB.Typ, OXB.realType, 0) END;
    IF ccWordsize = 8 THEN ss:="LONGREAL"; OXB.Enter( ss, OXB.Typ, OXB.doubleType, 0) END;
    ss:="REAL";   OXB.Enter( ss,    OXB.Typ,   OXB.realType, 0);
    IF ccWordsize = 4 THEN ss:="INTEGER"; OXB.Enter( ss,  OXB.Typ, OXB.intType, 0) END;
    IF ccWordsize = 8 THEN ss:="INTEGER"; OXB.Enter( ss,  OXB.Typ, OXB.longType, 0) END;
    ss:="INTEGER"; OXB.Enter( ss,  OXB.Typ,   OXB.intType, 0);
    IF ccWordsize = 8 THEN ss:="SHORTINT"; OXB.Enter(ss, OXB.Typ, OXB.shortType, 0) END;

    OXB.PrepSYSTEM;

    ss:="H";     OXB.Enter( ss,OXB.SFunc, OXB.intType, 201);     (*functions*)
    ss:="COND";  OXB.Enter( ss,OXB.SFunc, OXB.boolType, 191);
    ss:="SIZE";  OXB.Enter( ss,OXB.SFunc, OXB.intType, 181);
    ss:="ADR";   OXB.Enter( ss,OXB.SFunc, OXB.intType, 171);
    ss:="VAL";   OXB.Enter( ss,OXB.SFunc, OXB.intType, 162);
    ss:="REG";   OXB.Enter( ss,OXB.SFunc, OXB.intType, 151);
    ss:="BIT";   OXB.Enter( ss,OXB.SFunc, OXB.boolType, 142);
    ss:="REGREG";OXB.Enter( ss,OXB.SProc, OXB.noType, 212);  (*procedures*)
    ss:="LDREG"; OXB.Enter( ss,OXB.SProc, OXB.noType, 142);
    ss:="LDPSR"; OXB.Enter( ss,OXB.SProc, OXB.noType, 131);
    ss:="COPY";  OXB.Enter( ss,OXB.SProc, OXB.noType, 123);
    ss:="PUT";   OXB.Enter( ss,OXB.SProc, OXB.noType, 112);
    ss:="GET";   OXB.Enter( ss,OXB.SProc, OXB.noType, 102);
  END Prep;


  (* begin-procedure-description
---
**Compile** locates the source code to a module, initializes the scanner, and begins parsing at 'Module'.
  end-procedure-description *)
  PROCEDURE Compile*( f: ARRAY OF CHAR; o: ARRAY OF CHAR );
    VAR beg, end, time: INTEGER;
      T: Texts.Text;
      S: Texts.Scanner;
      ff: Texts.Filename;
      oo: Options; 
  BEGIN
    Emit("Compiling "); Emit( f ); Out.Ln;
        ff:= f; oo:=o;
        NEW(T); 
        Texts.Open(T, ff);
        IF T.len > 0 THEN
          Option(oo);  
	  Prep;
          NEW(dummy); dummy.class := OXB.Var; dummy.type := OXB.intType;
          expression := expression0; Type := Type0; FormalType := FormalType0;
          OXS.Init(T, 0, ccARCH, ccWordsize, ccStackalign);
          Module
        ELSE Emit( f); Emit( " not found");
          Out.Ln
        END

(*        IF (T.len # 0) & (OXS.errcnt = 0) THEN Texts.Scan(S) ELSE S.class := 0 END *)
   
(*    Oberon.Collect(0) *)
  END Compile;

  (* begin-procedure-description
---
**The initialzation code for this module** opens a writer to print marked errors and initializes the Oberon parser state.
  end-procedure-description *)
BEGIN Emit("Integrated Oberon Compiler  8.16.2021");
  Out.Ln;

kw:="IF"     ;  OXS.EnterKW(OXS.if,      kw,2);
kw:="DO"     ;  OXS.EnterKW(OXS.do,      kw,2);
kw:="OF"     ;  OXS.EnterKW(OXS.of,      kw,2);
kw:="OR"     ;  OXS.EnterKW(OXS.or,      kw,2);
kw:="TO"     ;  OXS.EnterKW(OXS.to,      kw,2);
kw:="IN"     ;  OXS.EnterKW(OXS.in,      kw,2);
kw:="IS"     ;  OXS.EnterKW(OXS.is,      kw,2);
kw:="BY"     ;  OXS.EnterKW(OXS.by,      kw,2);
kw:="END"    ;  OXS.EnterKW(OXS.end,     kw,3);
kw:="NIL"    ;  OXS.EnterKW(OXS.nil,     kw,3);
kw:="VAR"    ;  OXS.EnterKW(OXS.var,     kw,3);
kw:="DIV"    ;  OXS.EnterKW(OXS.div,     kw,3);
kw:="MOD"    ;  OXS.EnterKW(OXS.mod,     kw,3);
kw:="FOR"    ;  OXS.EnterKW(OXS.for,     kw,3);
kw:="ELSE"   ;  OXS.EnterKW(OXS.else,    kw,4);
kw:="THEN"   ;  OXS.EnterKW(OXS.then,    kw,4);
kw:="TRUE"   ;  OXS.EnterKW(OXS.true,    kw,4);
kw:="TYPE"   ;  OXS.EnterKW(OXS.type,    kw,4);
kw:="CASE"   ;  OXS.EnterKW(OXS.case,    kw,4);
kw:="ELSIF"  ;  OXS.EnterKW(OXS.elsif,   kw,5);
kw:="FALSE"  ;  OXS.EnterKW(OXS.false,   kw,5);
kw:="ARRAY"  ;  OXS.EnterKW(OXS.array,   kw,5);
kw:="BEGIN"  ;  OXS.EnterKW(OXS.begin,   kw,5);
kw:="CONST"  ;  OXS.EnterKW(OXS.const,   kw,5);
kw:="UNTIL"  ;  OXS.EnterKW(OXS.until,   kw,5);
kw:="WHILE"  ;  OXS.EnterKW(OXS.while,   kw,5);
kw:="RECORD" ;  OXS.EnterKW(OXS.record,  kw,6);
kw:="REPEAT" ;  OXS.EnterKW(OXS.repeat,  kw,6);
kw:="RETURN" ;  OXS.EnterKW(OXS.return,  kw,6);
kw:="IMPORT" ;  OXS.EnterKW(OXS.import,  kw,6);
kw:="MODULE" ;  OXS.EnterKW(OXS.module,  kw,6);
kw:="POINTER";  OXS.EnterKW(OXS.pointer, kw,7);
kw:=""       ;  OXS.EnterKW(OXS.notasymbol, kw,8);
kw:="PROCEDURE";  OXS.EnterKW(OXS.procedure, kw,9);
  OXS.SetCommentStyle(OXS.oberonstyle);
  OXS.SetSigCR(FALSE);
  OXS.SetSemiCR(FALSE);
  OXS.SetRunes(FALSE);

(*  NEW(dummy); dummy.class := OXB.Var; dummy.type := OXB.intType;
    expression := expression0; Type := Type0; FormalType := FormalType0 *)
END OXP.

