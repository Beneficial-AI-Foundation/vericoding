function sum(s: seq<int>) : int
    {
        if |s| == 0 then 0 else s[0] + sum(s[1..])
    }
function ceil(f: real) : (c : int)
    {
        (f + 1.0).Floor
    }
function square_seq(lst: seq<real>) : (sq : seq<int>)
        ensures |sq| == |lst|
    {
        seq(|lst|, i requires 0 <= i < |lst| => ceil(lst[i]) * ceil(lst[i]))
    }

// <vc-helpers>
lemma sum_append(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    calc {
      sum(s1 + s2);
      == { assert (s1 + s2)[0] == s1[0]; assert (s1 + s2)[1..] == s1[1..] + s2; }
      s1[0] + sum(s1[1..] + s2);
      == { sum_append(s1[1..], s2); }
      s1[0] + sum(s1[1..]) + sum(s2);
      == 
      sum(s1) + sum(s2);
    }
  }
}

lemma sum_empty()
  ensures sum([]) == 0
{
}

lemma sum_singleton(x: int)
  ensures sum([x]) == x
{
}

function f_square(x: real) : int
{
  ceil(x) * ceil(x)
}

lemma square_seq_lemma(lst: seq<real>)
  ensures square_seq(lst) == seq(|lst|, i requires 0 <= i < |lst| => f_square(lst[i]))
{
}

lemma square_seq_prefix(lst: seq<real>, n: int)
  requires 0 <= n <= |lst|
  ensures square_seq(lst[0..n]) == seq(n, i requires 0 <= i < n => f_square(lst[i]))
{
}

lemma square_seq_append(lst: seq<real>, n: int)
  requires 0 <= n < |lst|
  ensures square_seq(lst[0..n+1]) == square_seq(lst[0..n]) + [f_square(lst[n])]
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<real>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |lst| == 0 {
    r := 0;
    return;
  }
  
  var idx: int := 0;
  r := 0;
  var sq: seq<int> := [];
  
  while idx < |lst|
    invariant 0 <= idx <= |lst|
    invariant |sq| == idx
    invariant r == sum(sq)
    invariant sq == square_seq(lst[0..idx])
  {
    var head: real := lst[idx];
    var square_val: int := ceil(head) * ceil(head);
    sq := sq + [square_val];
    r := r + square_val;
    idx := idx + 1;
    
    // Prove the invariant is maintained
    assert square_seq(lst[0..idx]) == square_seq(lst[0..idx-1]) + [f_square(lst[idx-1])];
    assert sum(sq) == sum(square_seq(lst[0..idx-1])) + f_square(lst[idx-1]);
  }
  
  assert idx == |lst|;
  assert lst[0..idx] == lst;
}
// </vc-code>

