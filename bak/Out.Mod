MODULE Out;
    IMPORT SYSTEM;

    TYPE Str = ARRAY 32 OF CHAR;
 
    PROCEDURE String*(s: Str );
(**output a string.*)
    END String;

    PROCEDURE Int*(i, p: INTEGER );
(**output an integer.*)
    END Int;

    PROCEDURE Ln*;
(**output a newline.*)
    END Ln;

BEGIN
END Out.


