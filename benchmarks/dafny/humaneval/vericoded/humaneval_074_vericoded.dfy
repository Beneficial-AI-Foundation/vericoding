// <vc-preamble>

function total_chars(lst: seq<string>): nat
{
    if |lst| == 0 then 0
    else |lst[0]| + total_chars(lst[1..])
}
lemma total_chars_prefix(lst: seq<string>, i: nat)
    requires 0 <= i < |lst|
    ensures total_chars(lst[..i+1]) == total_chars(lst[..i]) + |lst[i]|
{
    if i == 0 {
        assert lst[..1] == [lst[0]];
        assert total_chars(lst[..1]) == |lst[0]| + total_chars([]);
        assert total_chars([]) == 0;
    } else {
        assert lst[..i+1] == [lst[0]] + (lst[1..])[..i];
        assert lst[..i] == [lst[0]] + (lst[1..])[..i-1];
        assert lst[i] == (lst[1..])[i-1];
        total_chars_prefix(lst[1..], i-1);
        assert total_chars((lst[1..])[..i]) == total_chars((lst[1..])[..i-1]) + |(lst[1..])[i-1]|;
        assert total_chars(lst[..i+1]) == |lst[0]| + total_chars((lst[1..])[..i]);
        assert total_chars(lst[..i]) == |lst[0]| + total_chars((lst[1..])[..i-1]);
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method total_match(lst1: seq<string>, lst2: seq<string>) returns (result: seq<string>)
    ensures result == lst1 || result == lst2
    ensures total_chars(lst1) <= total_chars(lst2) ==> result == lst1
    ensures total_chars(lst1) > total_chars(lst2) ==> result == lst2
// </vc-spec>
// <vc-code>
{
  var sum1 := 0;
  var i := 0;
  while i < |lst1|
    invariant 0 <= i <= |lst1|
    invariant sum1 == total_chars(lst1[..i])
  {
    sum1 := sum1 + |lst1[i]|;
    total_chars_prefix(lst1, i);
    i := i + 1;
  }
  assert lst1[..|lst1|] == lst1;
  assert sum1 == total_chars(lst1);
  
  var sum2 := 0;
  var j := 0;
  while j < |lst2|
    invariant 0 <= j <= |lst2|
    invariant sum2 == total_chars(lst2[..j])
  {
    sum2 := sum2 + |lst2[j]|;
    total_chars_prefix(lst2, j);
    j := j + 1;
  }
  assert lst2[..|lst2|] == lst2;
  assert sum2 == total_chars(lst2);
  
  if sum1 <= sum2 {
    result := lst1;
  } else {
    result := lst2;
  }
}
// </vc-code>
