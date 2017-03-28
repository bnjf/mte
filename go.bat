
@rem \tasm\bin\tasm /s /v /m \mte\mte.asm

copy \mte\mte.asm mte.asm
\tasm\bin\tasm /w+ /v /m mte
\tasm\bin\tlink /x /t demovir rnd mte

