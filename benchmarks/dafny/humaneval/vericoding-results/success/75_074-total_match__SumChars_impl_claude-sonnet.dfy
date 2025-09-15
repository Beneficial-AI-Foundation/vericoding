// <vc-preamble>
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma to properly handle sequence concatenation properties */
lemma SumCharsSliceLemma(list: seq<string>, i: int)
  requires 0 <= i < |list|
  ensures sum_chars_rec(list[..i+1]) == sum_chars_rec(list[..i]) + |list[i]|
{
  var prefix := list[..i];
  var extended := list[..i+1];
  assert extended == prefix + [list[i]];
  
  if |prefix| == 0 {
    assert prefix == [];
    assert extended == [list[i]];
    assert sum_chars_rec(prefix) == 0;
    assert sum_chars_rec(extended) == |list[i]| + sum_chars_rec([]);
    assert sum_chars_rec([]) == 0;
  } else {
    assert extended[0] == prefix[0];
    assert extended[1..] == prefix[1..] + [list[i]];
    
    calc {
      sum_chars_rec(extended);
    == |extended[0]| + sum_chars_rec(extended[1..]);
    == |prefix[0]| + sum_chars_rec(prefix[1..] + [list[i]]);
    }
    
    SumCharsConcatLemma(prefix[1..], [list[i]]);
    
    calc {
      sum_chars_rec(prefix[1..] + [list[i]]);
    == sum_chars_rec(prefix[1..]) + sum_chars_rec([list[i]]);
    == sum_chars_rec(prefix[1..]) + |list[i]|;
    }
    
    calc {
      sum_chars_rec(prefix);
    == |prefix[0]| + sum_chars_rec(prefix[1..]);
    }
  }
}

lemma SumCharsConcatLemma(a: seq<string>, b: seq<string>)
  ensures sum_chars_rec(a + b) == sum_chars_rec(a) + sum_chars_rec(b)
{
  if |a| == 0 {
    assert a + b == b;
    assert sum_chars_rec(a) == 0;
  } else {
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    SumCharsConcatLemma(a[1..], b);
  }
}
// </vc-helpers>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)

  ensures sum == sum_chars_rec(list)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): simplified implementation with explicit assertions */
{
  sum := 0;
  var i := 0;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant sum == sum_chars_rec(list[..i])
  {
    SumCharsSliceLemma(list, i);
    sum := sum + |list[i]|;
    i := i + 1;
  }
  assert i == |list|;
  assert list[..i] == list;
}
// </vc-code>
