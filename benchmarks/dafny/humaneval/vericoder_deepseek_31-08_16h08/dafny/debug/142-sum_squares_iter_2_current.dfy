function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}

// <vc-helpers>
lemma square_seq_definition(lst: seq<int>, i: int)
  requires 0 <= i < |lst|
  ensures square_seq(lst)[i] == (if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
{
}

lemma sum_recursive(s: seq<int>)
  ensures sum(s) == if |s| == 0 then 0 else s[0] + sum(s[1..])
{
}

lemma sum_append(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
  } else {
    sum_append(s1[1..], s2);
  }
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant r == sum(square_seq(lst[0..i]))
  {
    var elem := lst[i];
    var sq_elem: int;
    if i % 3 == 0 {
      sq_elem := elem * elem;
    } else if i % 4 == 0 {
      sq_elem := elem * elem * elem;
    } else {
      sq_elem := elem;
    }
    
    var current_slice := lst[0..i];
    var next_slice := lst[0..i+1];
    assert next_slice == current_slice + [lst[i]];
    assert square_seq(next_slice) == square_seq(current_slice) + [sq_elem];
    sum_append(square_seq(current_slice), [sq_elem]);
    
    r := r + sq_elem;
    i := i + 1;
  }
}
// </vc-code>

