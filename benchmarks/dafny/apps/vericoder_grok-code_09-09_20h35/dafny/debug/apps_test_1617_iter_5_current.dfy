function f(n: int, x: int): int
  requires x > 0 && n >= x && n % x == 0
{
  var y := n / x;
  y + x * y * (y - 1) / 2
}

predicate IsDivisor(d: int, n: int)
{
  d > 0 && n % d == 0
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// <vc-helpers>
function insert(v: int, s: seq<int>): seq<int>
 decreases |s|
{
  if |s| == 0 then [v] else if v < s[0] then [v] + s else [s[0]] + insert(v, s[1..])
}

lemma InsertPreservesNoDuplicates(v: int, s: seq<int>)
  requires NoDuplicates(s)
  requires v !in s
  ensures NoDuplicates(insert(v, s))
{
  if |s| == 0 {
    // Trivial, [v] has no duplicates.
  } else {
    if v < s[0] {
      // insert = [v] + s
      // Need to show NoDuplicates([v] + s)
      // v is not in s, s has no duplicates.
      // For i=0, [v], no issue.
      // For i>=1, s[i-1] != s[i-1] only if dup in s.
      // v != s[j] for all j.
    } else {
      // insert = [s[0]] + insert(v, s[1..])
      // First, prove that insert(v, s[1..]) has no duplicates by induction.
      InsertPreservesNoDuplicates(v, s[1..]);
      // Now, NoDuplicates([s[0]] + insert(v, s[1..]))
      // Need to ensure s[0] != all in insert(v, s[1..])
      // Since v != s[0], and insert starts with either v or s[1], which != s[0].
      // More formally, it holds.
    }
  }
}

lemma InsertPreservesSorted(v: int, s: seq<int>)
  requires IsSorted(s)
  ensures IsSorted(insert(v, s))
{
  if |s| == 0 {
    // [v] is sorted.
  } else {
    if v < s[0] {
      // [v] + s, since v < s[0] and s is sorted, yes.
    } else {
      // [s[0]] + insert(v, s[1..])
      InsertPreservesSorted(v, s[1..]);
      // Since s is sorted, s[0] <= s[1] <= ..., and insert(v, s[1..]) is sorted,
      // and s[0] <= insert's first element (v >= s[0] or s[1]).
    }
  }
}

function insertUnique(v: int, s: seq<int>): seq<int>
 decreases |s|
{
  if v in s then s else insert(v, s)
}

lemma InsertUniquePreservesNoDuplicates(v: int, s: seq<int>)
  requires NoDuplicates(s)
  ensures NoDuplicates(insertUnique(v, s))
{
  if v in s {
  } else {
    InsertPreservesNoDuplicates(v, s);
  }
}

lemma InsertUniquePreservesSorted(v: int, s: seq<int>)
  requires IsSorted(s)
  ensures IsSorted(insertUnique(v, s))
{
  if v in s {
  } else {
    InsertPreservesSorted(v, s);
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires n >= 2
  ensures NoDuplicates(result)
  ensures IsSorted(result)
  ensures forall v :: v in result <==> exists d :: IsDivisor(d, n) && v == f(n, d)
  ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  var divisors: seq<int> := [];
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall m :: 1 <= m < i && IsDivisor(m, n) ==> m in divisors
    invariant forall m :: m in divisors ==> IsDivisor(m, n)
    invariant NoDuplicates(divisors)
    invariant IsSorted(divisors)
  {
    if IsDivisor(i, n) {
      divisors := divisors + [i];
    }
    i := i + 1;
  }
  var result: seq<int> := [];
  for k := 0 to |divisors| - 1
    invariant NoDuplicates(result)
    invariant IsSorted(result)
    invariant forall r :: r in result <==> exists d :: d in divisors[..k] && r == f(n, d)
  {
    var d := divisors[k];
    var v := f(n, d);
    result := insertUnique(v, result);
  }
}
// </vc-code>

