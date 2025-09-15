// <vc-preamble>
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// </vc-preamble>

// <vc-helpers>
lemma NameInEnumeration(n: int)
  requires 1 <= n <= 9
  ensures NumberToName(n) in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
{
  match n
  case 1 => { assert NumberToName(n) == "One"; }
  case 2 => { assert NumberToName(n) == "Two"; }
  case 3 => { assert NumberToName(n) == "Three"; }
  case 4 => { assert NumberToName(n) == "Four"; }
  case 5 => { assert NumberToName(n) == "Five"; }
  case 6 => { assert NumberToName(n) == "Six"; }
  case 7 => { assert NumberToName(n) == "Seven"; }
  case 8 => { assert NumberToName(n) == "Eight"; }
  case 9 => { assert NumberToName(n) == "Nine"; }
}
// </vc-helpers>

// <vc-spec>
method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)

  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
// </vc-spec>
// <vc-code>
{
  var tmp: seq<string> := [];
  var i: int := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |tmp| <= i
    invariant forall j :: 0 <= j < |tmp| ==> tmp[j] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
    decreases |arr| - i
  {
    if 1 <= arr[i] && arr[i] <= 9 {
      NameInEnumeration(arr[i]);
      tmp := tmp + [NumberToName(arr[i])];
    }
    i := i + 1;
  }
  result := tmp;
}
// </vc-code>
