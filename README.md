# Build
Cross-compiler for an Oberon derived language

Requires the obnc Oberon to C translater from http://miasap.se/obnc/

Expects a 64-bit INTEGER and REAL, e.g. in /usr/local/include/obnc/OBNCConfig.h set the following:
```
#ifndef OBNC_CONFIG_C_INT_TYPE
#define OBNC_CONFIG_C_INT_TYPE OBNC_CONFIG_LONG_LONG
#endif

#ifndef OBNC_CONFIG_C_REAL_TYPE
#define OBNC_CONFIG_C_REAL_TYPE OBNC_CONFIG_LONG_DOUBLE
#endif
```
With obnc configured for 64-bit then:

`obnc oxpc.Mod`

That should recursively build the oxpc compiler.

Invoke the built compiler like this:

`./oxpc -v M.mod`

to build M.Mod for the 32-bit risc5 architecture.

### License of the io-port files

All source files except those specifically otherwise licensed are provided with the MIT License as detailed in the LICENSE file.

IO-core also incorporates source files from Project Oberon and are licensed as below:

### License of the Project Oberon files

Project Oberon, Revised Edition 2013

Book copyright (C)2013 Niklaus Wirth and Juerg Gutknecht;
software copyright (C)2013 Niklaus Wirth (NW), Juerg Gutknecht (JG), Paul
Reed (PR/PDR).

Permission to use, copy, modify, and/or distribute this software and its
accompanying documentation (the "Software") for any purpose with or
without fee is hereby granted, provided that the above copyright notice
and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHORS DISCLAIM ALL WARRANTIES
WITH REGARD TO THE SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY, FITNESS AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
AUTHORS BE LIABLE FOR ANY CLAIM, SPECIAL, DIRECT, INDIRECT, OR
CONSEQUENTIAL DAMAGES OR ANY DAMAGES OR LIABILITY WHATSOEVER, WHETHER IN
AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE DEALINGS IN OR USE OR PERFORMANCE OF THE SOFTWARE.


