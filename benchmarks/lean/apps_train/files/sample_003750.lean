The [half-life](https://en.wikipedia.org/wiki/Half-life) of a radioactive substance is the time it takes (on average) for one-half of its atoms to undergo radioactive decay.

# Task Overview
Given the initial quantity of a radioactive substance, the quantity remaining after a given period of time, and the period of time, return the half life of that substance. 

# Usage Examples

```if:csharp
Documentation:
Kata.HalfLife Method (Double, Double, Int32)

Returns the half-life for a substance given the initial quantity, the remaining quantity, and the elasped time.

Syntax

public
static
double HalfLife(
double quantityInitial,
    double quantityRemaining,
int time
    )

Parameters

quantityInitial

Type: System.Double
The initial amount of the substance.

quantityRemaining

Type: System.Double
The current amount of the substance.

time

Type: System.Int32
The amount of time elapsed.

Return Value

Type: System.Double
  A floating-point number representing the half-life of the substance.

```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
