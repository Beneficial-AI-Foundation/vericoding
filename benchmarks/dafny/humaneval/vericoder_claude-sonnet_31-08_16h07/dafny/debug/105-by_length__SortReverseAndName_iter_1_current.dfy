

// <vc-helpers>
lemma NumberToNameInRange(n: int)
  requires 1 <= n <= 9
  ensures NumberToName(n) in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
{
}

lemma FilterPreservesValidRange(s: seq<int>)
  ensures forall i :: 0 <= i < |FilterValidNumbers(s)| ==> 1 <= FilterValidNumbers(s)[i] <= 9
{
}

function FilterValidNumbers(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if 1 <= s[0] <= 9 then [s[0]] + FilterValidNumbers(s[1..])
  else FilterValidNumbers(s[1..])
}

lemma FilterSizeProperty(s: seq<int>)
  ensures |FilterValidNumbers(s)| <= |s|
{
  if |s| == 0 {
  } else {
    FilterSizeProperty(s[1..]);
  }
}

function ConvertToNames(s: seq<int>): seq<string>
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 9
  ensures |ConvertToNames(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> ConvertToNames(s)[i] == NumberToName(s[i])
  ensures forall i :: 0 <= i < |ConvertToNames(s)| ==> 
    ConvertToNames(s)[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
{
  if |s| == 0 then []
  else [NumberToName(s[0])] + ConvertToNames(s[1..])
}
// </vc-helpers>

// <vc-spec>
method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var filtered := FilterValidNumbers(arr);
  FilterSizeProperty(arr);
  FilterPreservesValidRange(arr);
  
  var sorted := SortSeq(filtered);
  var reversed := reverse(sorted);
  
  result := ConvertToNames(reversed);
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
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
// pure-end