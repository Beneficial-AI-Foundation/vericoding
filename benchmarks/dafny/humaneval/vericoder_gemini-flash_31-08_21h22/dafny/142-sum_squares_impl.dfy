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
function nth_square(lst: seq<int>, i: int) : int
  requires 0 <= i < |lst|
{
  if i % 3 == 0 then lst[i] * lst[i]
  else if i % 4 == 0 then lst[i] * lst[i] * lst[i]
  else lst[i]
}

function seq_nth_square(lst: seq<int>, k: int, len: int) : seq<int>
  requires 0 <= k <= |lst|
  requires 0 <= len
  requires k + len <= |lst|
{
  seq(len, i requires 0 <= i < len => nth_square(lst, k + i))
}

lemma SumSquareSeqLemma(lst: seq<int>, k: int)
  requires 0 <= k <= |lst|
  ensures sum(square_seq(lst)[k..]) == sum(seq_nth_square(lst, k, |lst| - k))
  decreases |lst| - k
{
  if k < |lst| {
    calc {
      sum(square_seq(lst)[k..]);
      square_seq(lst)[k] + sum(square_seq(lst)[k+1..]);
      {
        assert square_seq(lst)[k] == nth_square(lst, k);
      }
      nth_square(lst, k) + sum(square_seq(lst)[k+1..]);
      {
        SumSquareSeqLemma(lst, k+1);
      }
      nth_square(lst, k) + sum(seq_nth_square(lst, k + 1, |lst| - (k+1)));
      {
        assert forall i :: 0 <= i < |lst| - (k+1) ==> nth_square(lst, k + 1 + i) == seq_nth_square(lst, k+1, |lst|-(k+1))[i];
        assert seq(1, _ => nth_square(lst, k)) + seq(|lst|-(k+1), i requires 0 <= i < |lst|-(k+1) => nth_square(lst, k+1+i)) == seq_nth_square(lst, k, |lst|-k);
      }
      sum(seq_nth_square(lst, k, |lst| - k));
    }
  } else {
    assert sum(square_seq(lst)[k..]) == 0;
    assert sum(seq_nth_square(lst, k, |lst| - k)) == 0;
  }
}

lemma SumSeqOfNthSquare(lst: seq<int>, k: int, len: int)
  requires 0 <= k <= |lst|
  requires 0 <= len
  requires k + len <= |lst|
  ensures sum(seq_nth_square(lst, k, len)) == (if len == 0 then 0 else nth_square(lst, k) + sum(seq_nth_square(lst, k+1, len-1)))
{
  if len > 0 {
    calc {
      sum(seq_nth_square(lst, k, len));
      seq_nth_square(lst, k, len)[0] + sum(seq_nth_square(lst, k, len)[1..]);
      nth_square(lst, k) + sum(seq(len-1, i requires 0 <= i < len-1 => nth_square(lst, k + 1 + i)));
      nth_square(lst, k) + sum(seq_nth_square(lst, k+1, len-1));
    }
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
    var r_sum_squares := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant r_sum_squares == sum(square_seq(lst)[0..i])
    {
        assert square_seq(lst)[i] == nth_square(lst, i);
        r_sum_squares := r_sum_squares + nth_square(lst, i);
        assert sum(square_seq(lst)[0..i+1]) == sum(square_seq(lst)[0..i]) + square_seq(lst)[i]; // This assertion needs to be proved
        i := i + 1;
    }
    assert r_sum_squares == sum(square_seq(lst)[0..|lst|]);
    return r_sum_squares;
}
// </vc-code>

