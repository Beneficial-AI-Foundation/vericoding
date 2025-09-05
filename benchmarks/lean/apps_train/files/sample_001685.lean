A group of N golfers wants to play in groups of G players for D days in such a way that no golfer plays more than once with any other golfer. For example, for N=20, G=4, D=5, the solution at Wolfram MathWorld is

```
 Mon:   ABCD    EFGH    IJKL    MNOP    QRST
 Tue:   AEIM    BJOQ    CHNT    DGLS    FKPR
 Wed:   AGKO    BIPT    CFMS    DHJR    ELNQ
 Thu:   AHLP    BKNS    CEOR    DFIQ    GJMT
 Fri:   AFJN    BLMR    CGPQ    DEKT    HIOS
```

Write a function that validates a proposed solution, a list of list of strings, as being a solution to the social golfer problem. Each character represents a golfer, and each string is a group of players. Rows represent days. The solution above would be encoded as:

```
 [
  ['ABCD', 'EFGH', 'IJKL', 'MNOP', 'QRST'],
  ['AEIM', 'BJOQ', 'CHNT', 'DGLS', 'FKPR'],
  ['AGKO', 'BIPT', 'CFMS', 'DHJR', 'ELNQ'],
  ['AHLP', 'BKNS', 'CEOR', 'DFIQ', 'GJMT'],
  ['AFJN', 'BLMR', 'CGPQ', 'DEKT', 'HIOS']
 ]
```

You need to make sure (1) that each golfer plays exactly once every day, (2) that the number and size of the groups is the same every day, and (3) that each player plays with every other player *at most* once.

So although each player must play every day, there can be particular pairs of players that never play together.

It is not necessary to consider the case where the number of golfers is zero; no tests will check for that. If you do wish to consider that case, note that you should accept as valid all possible solutions for zero golfers, who (vacuously) can indeed play in an unlimited number of groups of zero.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded