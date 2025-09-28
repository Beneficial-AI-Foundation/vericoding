// <vc-preamble>
predicate ValidThreeIntegers(input: string, a: int, b: int, c: int)
{
    var parts := SplitBySpacesFunc(input);
    |parts| == 3 && 
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    ParseIntFunc(parts[0]) == a &&
    ParseIntFunc(parts[1]) == b &&
    ParseIntFunc(parts[2]) == c
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] != '-' || |s| > 1) &&
    (s[0] == '-' ==> forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9') &&
    (s[0] != '-' ==> forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function SplitBySpacesFunc(s: string): seq<string>
{
    SplitBySpacesHelper(s, 0, "", [])
}

function SplitBySpacesHelper(s: string, i: int, current: string, parts: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then parts + [current] else parts
    else if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' then
        if |current| > 0 then
            SplitBySpacesHelper(s, i + 1, "", parts + [current])
        else
            SplitBySpacesHelper(s, i + 1, current, parts)
    else
        SplitBySpacesHelper(s, i + 1, current + [s[i]], parts)
}

function ParseIntFunc(s: string): int
    requires |s| > 0
    requires IsValidInteger(s)
{
    if |s| > 0 && s[0] == '-' then
        -ParseUnsignedInt(s[1..])
    else
        ParseUnsignedInt(s)
}

function ParseUnsignedInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else ParseUnsignedInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper function `IsArithmeticProgression` is unchanged. */
function IsArithmeticProgression(a: int, b: int, c: int): bool {
  a + c == 2 * b
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures (exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c)) ==> 
            (result == "YES\n" || result == "NO\n")
    ensures (exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c)) ==> 
            (exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c) && 
             (result == "YES\n" <==> b - a == c - b))
    ensures !(exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c)) ==> 
            result == ""
    ensures (forall a1: int, b1: int, c1: int, a2: int, b2: int, c2: int ::
        ValidThreeIntegers(input, a1, b1, c1) && ValidThreeIntegers(input, a2, b2, c2) ==>
        a1 == a2 && b1 == b2 && c1 == c2)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous implementation had errors related to assigning to non-ghost variables in a ghost context and assigning to variables not declared within the `forall` statement. To fix this, I've re-structured the `if` block. Instead of trying to extract `a_val`, `b_val`, `c_val` within a `forall` statement, I'm now finding them directly using an `if-then-else` structure with `exists` and `by`. This allows me to assign the values correctly and then use them to determine the `result`. The logic to determine if the numbers form an arithmetic progression and set the result accordingly remains the same. */
{
  var a: int := 0;
  var b: int := 0;
  var c: int := 0;

  if (exists a': int, b': int, c': int :: ValidThreeIntegers(input, a', b', c')) {
    if (true) by (a', b', c': int | ValidThreeIntegers(input, a', b', c') entails true) {
      // The ensures clause guarantees that a, b, c are unique if they exist, so we can pick any.
      // We can use an arbitrary choice for a', b', c' here.
      var a_prime: int, b_prime: int, c_prime: int;
      if (exists a_tmp: int, b_tmp: int, c_tmp: int :: ValidThreeIntegers(input, a_tmp, b_tmp, c_tmp)) {
        a_prime := a_tmp;
        b_prime := b_tmp;
        c_prime := c_tmp;
      }
    
      a := a_prime;
      b := b_prime;
      c := c_prime;
    }

    if IsArithmeticProgression(a, b, c) {
      result := "YES\n";
    } else {
      result := "NO\n";
    }
  } else {
    result := "";
  }
}
// </vc-code>
