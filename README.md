# UnitsCurvesF2

This is the Macaulay2 code accompanying the paper [Units of Hyperelliptic Curves over 𝔽2](https://arxiv.org/abs/2306.04838).
A typical session is shown below:

```
i1 : load "UnitsHyperellipticCurves.m2"

i2 : S = ZZ/2[x]; (g,h) = (x^6,x+1)

       6
o3 = (x , x + 1)

o3 : Sequence

i4 : elapsedTime (a,b) = fundamentalUnit (g,h, Degree=>{79})
Searching for units in degree 79... -- 0.311761 seconds elapsed

       74    73    68    67    63    61    57    56    52    51    45    43  
o4 = (x   + x   + x   + x   + x   + x   + x   + x   + x   + x   + x   + x   +
     ------------------------------------------------------------------------
      40    37    35    32    29    27    24    21    19    16    13    11  
     x   + x   + x   + x   + x   + x   + x   + x   + x   + x   + x   + x   +
     ------------------------------------------------------------------------
      8    5       79    73    61    57    45    37    29    21    13    5
     x  + x  + 1, x   + x   + x   + x   + x   + x   + x   + x   + x   + x )

i5 : a^2 + a*b*g + b^2*h

o5 = 1

o5 : S
```
