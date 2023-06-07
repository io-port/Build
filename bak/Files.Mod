MODULE Files;
 

  CONST
    READ = 0;
    WRITE = 1;
    APPEND = 2;

  TYPE
    FileDesc = RECORD i: INTEGER END;
    File*   = POINTER TO FileDesc;
    Filename* = ARRAY 32 OF CHAR;
    Rider* =
      RECORD eof*: BOOLEAN;
        res*: INTEGER;
        file: File;
        apos, bpos: INTEGER;
(*        buf: Buffer;  *)
(*        Ot: OT;       *)
      END ;

  VAR 
    initialized: INTEGER;


    PROCEDURE Init*(VAR arg: Filename);
(**initialized the files subsystem.*)
    END Init;

    PROCEDURE Exists*(filename: Filename) : INTEGER;
(**checks for the existence of a file by name.*)
    RETURN 0
    END Exists;

    PROCEDURE Timestamp*(filename: Filename) : INTEGER;
(**retrieves the timestamp of a file by name.*)
    RETURN 0
    END Timestamp;

    PROCEDURE New*(filename: Filename) : File;
(**Create a new file with name.*)
    RETURN NIL
    END New;

    PROCEDURE Old*(filename: Filename) : File;
(**retrieve an existing file file by name.*)
    RETURN NIL
    END Old;

    PROCEDURE Close*(f: File);
(**close a file.*)
    END Close;

    PROCEDURE Register*(f: File);
(**register a file in the file directory structure.*)
    END Register;

    PROCEDURE Move*(sourceFilename: Filename; destFilename: Filename);
(**rename an existing file.*)
    END Move;

    PROCEDURE Remove*(filename: Filename);
(**removes a file by name.*)
    END Remove;

    PROCEDURE CreateDir*(dirname: Filename);
(**creates a directory.*)
    END CreateDir;

    PROCEDURE Read*(VAR x: Rider; VAR b: BYTE);
(**read from a file.*)
    END Read;

    PROCEDURE ReadString*(VAR r: Rider; VAR s: Filename );
(**read from a file.*)
    END ReadString;

    PROCEDURE Write*(VAR x: Rider; i: INTEGER);
(**write a char or byte? to a file.*)
    END Write;

    PROCEDURE WriteInt*(VAR x: Rider; i: INTEGER);
(**write an INTEGER to a file.*)
    END WriteInt;

    PROCEDURE WriteString*(VAR r: Rider; s: Filename );
(**write to a file.*)
    END WriteString;

    PROCEDURE Set*(VAR x: Rider; f: File; i: INTEGER);
(**set a file cursor.*)
    END Set;

    PROCEDURE Length*(VAR f: File): INTEGER;
(**retrieve the length of a file.*)
    RETURN 0
    END Length;

    PROCEDURE Pos*(VAR r: Rider): INTEGER;
(**retrieve the position of a rider in a file.*)
    RETURN 0
    END Pos;

    PROCEDURE Base*(VAR r: Rider): File;
(**retrieve the base file from a rider.*)
    RETURN NIL
    END Base;


BEGIN
END Files.


