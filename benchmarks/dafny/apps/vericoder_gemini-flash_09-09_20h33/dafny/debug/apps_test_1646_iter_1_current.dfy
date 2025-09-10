predicate ValidBinaryString(s: string)
{
    |s| > 0 && 
    (forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1') &&
    (s == "0" || s[0] == '1')
}

function count_zeros(s: string): int
    ensures count_zeros(s) >= 0
    ensures count_zeros(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == '0' then 1 else 0) + count_zeros(s[1..])
}

predicate IsMinimalForm(s: string, result: string)
{
    s == "0" ==> result == "0"
    &&
    s != "0" ==> result == "1" + seq(count_zeros(s), _ => '0')
}

// <vc-helpers>
function seq<T>(len: int, f: int -> T): seq<T>
  requires len >= 0
  ensures |seq(len, f)| == len
{
  if len == 0 then [] else [f(0)] + seq(len - 1, x => f(x + 1))
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires n >= 1 && n <= 100
    requires |s| == n
    requires ValidBinaryString(s)
    ensures ValidBinaryString(result)
    ensures IsMinimalForm(s, result)
// </vc-spec>
// <vc-code>
{
  if s == "0" then
    result := "0";
  else
    var zeros := count_zeros(s);
    result := "1";
    for i := 0 to zeros - 1
      ensures |result| - 1 == i
      decreases zeros - i
    {
      result := result + "0";
    }
}
// </vc-code>

