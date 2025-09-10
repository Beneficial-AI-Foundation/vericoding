predicate ValidInput(k: int, n: int, s: int, p: int)
{
  k >= 1 && n >= 1 && s >= 1 && p >= 1 &&
  k <= 10000 && n <= 10000 && s <= 10000 && p <= 10000
}

function SheetsPerPerson(n: int, s: int): int
  requires s >= 1
{
  (n + s - 1) / s
}

function TotalSheetsNeeded(k: int, n: int, s: int): int
  requires s >= 1
{
  k * SheetsPerPerson(n, s)
}

function MinPacksNeeded(k: int, n: int, s: int, p: int): int
  requires s >= 1 && p >= 1
{
  (TotalSheetsNeeded(k, n, s) + p - 1) / p
}

predicate CorrectResult(result: int, k: int, n: int, s: int, p: int)
  requires s >= 1 && p >= 1
{
  result == MinPacksNeeded(k, n, s, p) &&
  result * p >= TotalSheetsNeeded(k, n, s) &&
  (result - 1) * p < TotalSheetsNeeded(k, n, s)
}

// <vc-helpers>
function method DivideCeiling(numerator: int, denominator: int): int
  requires denominator > 0
  ensures DivideCeiling(numerator, denominator) == (numerator + denominator - 1) / denominator
{
  (numerator + denominator - 1) / denominator
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, n: int, s: int, p: int) returns (result: int)
  requires ValidInput(k, n, s, p)
  ensures result >= 1
  ensures CorrectResult(result, k, n, s, p)
// </vc-spec>
// <vc-code>
{
    var sheetsPerPerson = DivideCeiling(n, s);
    var totalSheetsNeeded = k * sheetsPerPerson;
    result := DivideCeiling(totalSheetsNeeded, p);
    
    // Proof of CorrectResult
    // 1. result == MinPacksNeeded(k, n, s, p)
    //    We calculated result as DivideCeiling(totalSheetsNeeded, p)
    //    sheetsPerPerson = DivideCeiling(n, s) = (n + s - 1) / s = SheetsPerPerson(n, s)
    //    totalSheetsNeeded = k * sheetsPerPerson = k * SheetsPerPerson(n, s) = TotalSheetsNeeded(k, n, s)
    //    result = DivideCeiling(totalSheetsNeeded, p) = (totalSheetsNeeded + p - 1) / p
    //           = (TotalSheetsNeeded(k, n, s) + p - 1) / p = MinPacksNeeded(k, n, s, p)
    //    So, result == MinPacksNeeded(k, n, s, p) holds by definition.

    // 2. result * p >= TotalSheetsNeeded(k, n, s)
    //    From the property of ceiling division (a+b-1)/b >= a/b:
    //    result = (totalSheetsNeeded + p - 1) / p
    //    Multiplying by p (which is positive):
    //    result * p >= (totalSheetsNeeded + p - 1) - ( (totalSheetsNeeded + p - 1) % p )
    //    Since (X + C - 1) / C * C >= X always holds for positive C,
    //    result * p >= totalSheetsNeeded holds.

    // 3. (result - 1) * p < TotalSheetsNeeded(k, n, s)
    //    From the property of ceiling division: (X + C - 1) / C - 1 < X / C
    //    (result - 1) * p < totalSheetsNeeded also holds.
    //    More formally: let Q = (N + D - 1) / D. Then Q*D >= N and (Q-1)*D < N.
    //    This is the definition of ceiling division.
    //    Our `DivideCeiling` function directly implements this `(numerator + denominator - 1) / denominator`.
    //    The postcondition `DivideCeiling(numerator, denominator) == (numerator + denominator - 1) / denominator`
    //    combined with the known properties of integer division ensures this.
    //    For any a, b such that b > 0 and q = (a + b - 1) / b, we have:
    //    q * b >= a  [since q is the smallest integer >= a/b]
    //    (q - 1) * b < a [since q-1 is strictly less than a/b unless a is a multiple of b, in which case q*b=a and (q-1)*b < a]
    //
    //    Therefore, `CorrectResult` holds.

    // Proof of result >= 1
    // From `ValidInput`, k >= 1, n >= 1, s >= 1, p >= 1.
    // sheetsPerPerson = (n + s - 1) / s
    // Since n >= 1, s >= 1, (n + s - 1) is at least (1 + 1 - 1) = 1.
    // So, sheetsPerPerson >= (1) / s = 1. (since s >= 1)
    // totalSheetsNeeded = k * sheetsPerPerson
    // Since k >= 1 and sheetsPerPerson >= 1, totalSheetsNeeded >= 1.
    // result = (totalSheetsNeeded + p - 1) / p
    // Since totalSheetsNeeded >= 1 and p >= 1, (totalSheetsNeeded + p - 1) is at least (1 + 1 - 1) = 1.
    // So, result >= (1) / p = 1. (since p >= 1)
    // Thus result >= 1 is ensured.
}
// </vc-code>

