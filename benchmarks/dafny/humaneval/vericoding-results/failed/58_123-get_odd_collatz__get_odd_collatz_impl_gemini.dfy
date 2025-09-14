// <vc-preamble>
function iterate_to_odd(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2)
}
function next_odd_collatz(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd(n) else iterate_to_odd(3 * n + 1)
}
// </vc-preamble>

// <vc-helpers>
predicate sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 3): fixed ensures clauses to refer to the function call, not 'result' */
function insert(s: seq<int>, val: int): seq<int>
  requires sorted(s)
  ensures sorted(insert(s, val))
  ensures multiset(insert(s, val)) == multiset(s) + multiset({val})
{
  if |s| == 0 then [val]
  else if val <= s[0] then [val] + s
  else [s[0]] + insert(s[1..], val)
}

/* helper modified by LLM (iteration 3): fixed ensures clauses to refer to the function call, not 'result' */
function sort(s: seq<int>): seq<int>
  ensures sorted(sort(s))
  ensures multiset(sort(s)) == multiset(s)
{
  if |s| == 0 then []
  else insert(sort(s[1..]), s[0])
}
// </vc-helpers>

// <vc-spec>
method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): no change; logic is correct with fixed helpers */
  var current: nat := n;
  if current % 2 == 0 {
    current := iterate_to_odd(current);
  }

  var generated_seq: seq<int> := [current as int];

  while current != 1
    invariant current > 0 && current % 2 == 1
    invariant forall x :: x in generated_seq ==> x > 0 && x % 2 == 1
  {
    current := next_odd_collatz(current);
    generated_seq := generated_seq + [current as int];
  }

  sorted := sort(generated_seq);
}
// </vc-code>
