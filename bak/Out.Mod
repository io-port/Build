MODULE Out;
    IMPORT SYSTEM;

    TYPE Str = ARRAY 128 OF CHAR;
 
    PROCEDURE String*(s: Str );
(**output a string.*)
    END String;

    PROCEDURE Int*(i, p: INTEGER );
(**output an integer.*)
    END Int;

    PROCEDURE Hex*(h: INTEGER );
(**output a hex value.*)
    END Hex;

    PROCEDURE Ln*;
(**output a newline.*)
    END Ln;

BEGIN
END Out.


