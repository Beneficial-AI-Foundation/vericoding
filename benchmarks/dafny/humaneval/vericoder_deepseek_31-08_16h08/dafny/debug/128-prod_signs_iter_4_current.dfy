function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
  ensures x >= 0 ==> abs(x) == x
  ensures x < 0 ==> abs(x) == -x
{
  if x >= 0 then x else -x
}
function sum_abs(s: seq<int>) : int
  ensures sum_abs(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_abs(s[1..])
}

// <vc-helpers>
lemma {:induction s} SumAbsProperties(s: seq<int>)
  ensures sum_abs(s) >= 0
  ensures forall i :: 0 <= i < |s| ==> abs(s[i]) <= sum_abs(s)
  decreases |s|
{
  if |s| > 0 {
    SumAbsProperties(s[1..]);
  }
}

lemma SignLemma(count: int)
  ensures count % 2 == 0 ==> 1 >= 0
  ensures count % 2 == 1 ==> -1 <= 0
{
}

lemma ProductSignLemma(negCount: int, s: int)
  requires negCount % 2 == 0 ==> s >= 0
  requires negCount % 2 == 1 ==> s <= 0
  ensures abs(s) == s || abs(s) == -s
{
}

lemma AbsProductLemma(a: int, b: int)
  ensures abs(a * b) == abs(a) * abs(b)
{
}

lemma SumAbsSliceLemma(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sum_abs(s[0..i]) + sum_abs(s[i..]) == sum_abs(s)
  decreases |s|
{
  if i > 0 && |s| > 0 {
    SumAbsSliceLemma(s[1..], i-1);
  }
}

lemma SumAbsConsLemma(s: seq<int>)
  requires |s| > 0
  ensures sum_abs(s) == abs(s[0]) + sum_abs(s[1..])
{
}

lemma AbsPreservesSign(x: int)
  ensures abs(x) >= 0
{
}

lemma AbsNonNegative(x: int)
  ensures abs(x) >= 0
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
// </vc-spec>
// <vc-code>
{
  if |numbers| == 0 {
    s := 0;
  } else {
    var negCount := 0;
    s := 1;
    var i := 0;
    while i < |numbers|
      invariant 0 <= i <= |numbers|
      invariant negCount == |set j | 0 <= j < i && numbers[j] < 0|
      invariant abs(s) == sum_abs(numbers[0..i])
      invariant negCount % 2 == 0 ==> s >= 0
      invariant negCount % 2 == 1 ==> s <= 0
    {
      var current := numbers[i];
      var current_abs := abs(current);
      
      if current < 0 {
        negCount := negCount + 1;
      }
      
      s := s * current_abs;
      
      if negCount % 2 == 1 {
        s := -s;
      }
      
      i := i + 1;
    }
  }
}
// </vc-code>

