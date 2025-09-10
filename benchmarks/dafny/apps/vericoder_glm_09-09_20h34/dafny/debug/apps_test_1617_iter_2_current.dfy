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
function InsertionSort(s: seq<int>): seq<int>
  ensures IsSorted(InsertionSort(s))
  ensures multiset(InsertionSort(s)) == multiset(s)
  decreases |s|
{
  if |s| <= 1 then s
  else
    var sortedRest := InsertionSort(s[1..]);
    Insert(sortedRest, s[0])
}

function Insert(s: seq<int>, x: int): seq<int>
  requires IsSorted(s)
  ensures IsSorted(Insert(s, x))
  ensures multiset(Insert(s, x)) == multiset(s) + {x}
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(s[1..], x)
}
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
  var s := {};
  for d := 1 to n
    invariant s == set d0 | 0 < d0 <= d && n % d0 == 0 :: f(n, d0)
  {
    if n % d == 0 {
      var y := n / d;
      var v := y + d * y * (y - 1) / 2;
      s := s + {v};
    }
  }

  var resultSeq := [];
  var temp := s;
  while temp != {}
  {
    var v :| v in temp;
    resultSeq := resultSeq + [v];
    temp := temp - {v};
  }

  result := InsertionSort(resultSeq);
}
// </vc-code>

