// <vc-preamble>

function countEven(lst: seq<int>): int
    ensures countEven(lst) >= 0
    ensures countEven(lst) <= |lst|
{
    if |lst| == 0 then 0
    else if lst[0] % 2 == 0 then 1 + countEven(lst[1..])
    else countEven(lst[1..])
}

predicate ValidInput(lst1: seq<int>, lst2: seq<int>)
{
    |lst1| > 0 && |lst2| > 0
}

predicate CanExchange(lst1: seq<int>, lst2: seq<int>)
{
    countEven(lst1) + countEven(lst2) >= |lst1|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemmas for countEven non-negativity and upper bound */
lemma CountEvenNonNeg(lst: seq<int>)
  ensures countEven(lst) >= 0
  decreases |lst|
{
  if |lst| == 0 {
  } else {
    CountEvenNonNeg(lst[1..]);
    if lst[0] % 2 == 0 {
      assert countEven(lst) == 1 + countEven(lst[1..]);
      assert countEven(lst[1..]) >= 0;
      assert countEven(lst) >= 0;
    } else {
      assert countEven(lst) == countEven(lst[1..]);
      assert countEven(lst[1..]) >= 0;
      assert countEven(lst) >= 0;
    }
  }
}

/* helper modified by LLM (iteration 2): lemma showing countEven <= length */
lemma CountEvenLeLen(lst: seq<int>)
  ensures countEven(lst) <= |lst|
  decreases |lst|
{
  if |lst| == 0 {
  } else {
    CountEvenLeLen(lst[1..]);
    if lst[0] % 2 == 0 {
      assert countEven(lst) == 1 + countEven(lst[1..]);
      assert countEven(lst[1..]) <= |lst[1..]|;
      assert 1 + |lst[1..]| == |lst|;
      assert countEven(lst) <= |lst|;
    } else {
      assert countEven(lst) == countEven(lst[1..]);
      assert countEven(lst[1..]) <= |lst[1..]|;
      assert countEven(lst) <= |lst|;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method exchange(lst1: seq<int>, lst2: seq<int>) returns (result: string)
    requires ValidInput(lst1, lst2)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanExchange(lst1, lst2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): return "YES" iff enough even numbers to exchange */
  var ce1 := countEven(lst1);
  var ce2 := countEven(lst2);
  if ce1 + ce2 >= |lst1| {
    result := "YES";
  } else {
    result := "NO";
  }
}

// </vc-code>
