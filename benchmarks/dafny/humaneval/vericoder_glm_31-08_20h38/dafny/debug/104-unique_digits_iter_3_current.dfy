function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
function InsertSorted(x: int, s: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |InsertSorted(x,s)| ==> InsertSorted(x,s)[i] <= InsertSorted(x,s)[j]
  ensures multiset(InsertSorted(x,s)) == multiset(s) + {x}
  decreases s
{
  if |s| == 0 then [x]
  else
    if x <= s[0] then [x] + s
    else [s[0]] + InsertSorted(x, s[1..])
}
// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if (|x| == 0) then
    result := [];
  else {
    var rest := UniqueDigits(x[1..]);
    if (HasNoEvenDigit(x[0])) then
      result := InsertSorted(x[0], rest);
    else
      result := rest;
  }
}
// </vc-code>

