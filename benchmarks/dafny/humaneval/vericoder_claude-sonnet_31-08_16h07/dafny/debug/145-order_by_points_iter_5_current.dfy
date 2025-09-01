function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
lemma digits_sum_stable(a: int, b: int)
  ensures digits_sum(a) == digits_sum(b) ==> digits_sum(a) <= digits_sum(b)
{
}

lemma sort_maintains_multiset<T>(s: seq<T>, sorted: seq<T>)
  requires |s| == |sorted|
  requires multiset(s) == multiset(sorted)
  ensures multiset(s) == multiset(sorted)
{
}

lemma swap_preserves_multiset<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}

lemma insertion_maintains_sorted_order(sorted: seq<int>, j: int, i: int)
  requires 0 <= j <= i < |sorted|
  requires forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
  requires j == 0 || digits_sum(sorted[j-1]) <= digits_sum(sorted[j])
  requires forall x :: j < x <= i ==> digits_sum(sorted[j]) <= digits_sum(sorted[x])
  ensures forall x, y :: 0 <= x < y <= i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
{
  if j == 0 {
    assert forall x, y :: 0 <= x < y <= i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y]);
  } else {
    assert forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y]);
    assert digits_sum(sorted[j-1]) <= digits_sum(sorted[j]);
    assert forall x :: j < x <= i ==> digits_sum(sorted[j]) <= digits_sum(sorted[x]);
    
    forall x, y | 0 <= x < y <= i
      ensures digits_sum(sorted[x]) <= digits_sum(sorted[y])
    {
      if y < i {
        assert digits_sum(sorted[x]) <= digits_sum(sorted[y]);
      } else if y == i {
        if x < j {
          if j < i {
            assert digits_sum(sorted[x]) <= digits_sum(sorted[j]);
            assert digits_sum(sorted[j]) <= digits_sum(sorted[i]);
          } else {
            assert digits_sum(sorted[x]) <= digits_sum(sorted[i]);
          }
        } else if x == j {
          assert digits_sum(sorted[j]) <= digits_sum(sorted[i]);
        } else {
          assert digits_sum(sorted[x]) <= digits_sum(sorted[i]);
        }
      }
    }
  }
}

lemma sorted_order_preserved_around_insertion(sorted: seq<int>, j: int, i: int)
  requires 0 <= j <= i < |sorted|
  requires forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
  requires forall x :: j < x <= i ==> digits_sum(sorted[j]) <= digits_sum(sorted[x])
  requires j == 0 || digits_sum(sorted[j-1]) <= digits_sum(sorted[j])
  ensures forall x, y :: 0 <= x < y < |sorted| && (y <= j || x > i) ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
{
}

lemma swap_maintains_sorted_prefix(sorted: seq<int>, j: int, i: int)
  requires 0 < j <= i < |sorted|
  requires forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
  requires digits_sum(sorted[j-1]) > digits_sum(sorted[j])
  requires forall x :: j < x <= i ==> digits_sum(sorted[j]) <= digits_sum(sorted[x])
  ensures forall x, y :: 0 <= x < y < i ==> 
    digits_sum((sorted[j-1 := sorted[j]][j := sorted[j-1]])[x]) <= 
    digits_sum((sorted[j-1 := sorted[j]][j := sorted[j-1]])[y])
{
  var new_sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
  
  forall x, y | 0 <= x < y < i
    ensures digits_sum(new_sorted[x]) <= digits_sum(new_sorted[y])
  {
    if x == j-1 && y == j {
      assert digits_sum(new_sorted[x]) == digits_sum(sorted[j]);
      assert digits_sum(new_sorted[y]) == digits_sum(sorted[j-1]);
      assert digits_sum(sorted[j-1]) > digits_sum(sorted[j]);
    } else if x == j-1 && y != j {
      assert y > j;
      assert digits_sum(new_sorted[x]) == digits_sum(sorted[j]);
      assert digits_sum(new_sorted[y]) == digits_sum(sorted[y]);
      assert digits_sum(sorted[j]) <= digits_sum(sorted[y]);
    } else if x != j-1 && y == j {
      assert x < j-1;
      assert digits_sum(new_sorted[x]) == digits_sum(sorted[x]);
      assert digits_sum(new_sorted[y]) == digits_sum(sorted[j-1]);
      assert digits_sum(sorted[x]) <= digits_sum(sorted[j-1]);
    } else {
      assert digits_sum(new_sorted[x]) == digits_sum(sorted[x]);
      assert digits_sum(new_sorted[y]) == digits_sum(sorted[y]);
      assert digits_sum(sorted[x]) <= digits_sum(sorted[y]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    sorted := [];
    return;
  }
  
  sorted := s;
  
  var i := 1;
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
  {
    var j := i;
    while j > 0 && digits_sum(sorted[j-1]) > digits_sum(sorted[j])
      invariant 0 <= j <= i
      invariant |sorted| == |s|
      invariant multiset(s) == multiset(sorted)
      invariant forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
      invariant forall x :: j < x <= i ==> digits_sum(sorted[j]) <= digits_sum(sorted[x])
    {
      swap_preserves_multiset(sorted, j-1, j);
      swap_maintains_sorted_prefix(sorted, j, i);
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    
    insertion_maintains_sorted_order(sorted, j, i);
    i := i + 1;
  }
}
// </vc-code>

