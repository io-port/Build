MODULE Files;
 

  CONST
    READ = 0;
    WRITE = 1;
    APPEND = 2;

  TYPE
    FileDesc = RECORD i: INTEGER END;
    FILE = POINTER TO FileDesc;

  VAR 
    initialized: INTEGER;


    PROCEDURE Init*(VAR arg: ARRAY OF CHAR);
(**initialized the files subsystem.*)
    END Init;

    PROCEDURE Exists*(filename: ARRAY OF CHAR) : INTEGER;
(**checks for the existence of a file by name.*)
    RETURN 0
    END Exists;

    PROCEDURE Timestamp*(filename: ARRAY OF CHAR) : INTEGER;
(**retrieves the timestamp of a file by name.*)
    RETURN 0
    END Timestamp;

    PROCEDURE New*(filename: ARRAY OF CHAR) : FILE;
(**Create a new file with name.*)
    RETURN NIL
    END New;

    PROCEDURE Old*(filename: ARRAY OF CHAR; mode: INTEGER) : FILE;
(**retrieve an existing file file by name.*)
    RETURN NIL
    END Old;

    PROCEDURE Close*(file: FILE);
(**close a file.*)
    END Close;

    PROCEDURE Move*(sourceFilename: ARRAY OF CHAR; destFilename: ARRAY OF CHAR);
(**rename an existing file.*)
    END Move;

    PROCEDURE Remove*(filename: ARRAY OF CHAR);
(**removes a file by name.*)
    END Remove;

    PROCEDURE CreateDir*(dirname: ARRAY OF CHAR);
(**creates a directory.*)
    END CreateDir;


BEGIN
END Files.


