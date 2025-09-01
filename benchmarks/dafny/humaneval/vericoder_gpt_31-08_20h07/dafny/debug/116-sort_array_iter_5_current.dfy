function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
predicate AdjSortedByPopcount(a: seq<nat>)
  decreases |a|
{
  |a| <= 1 || (popcount(a[0]) <= popcount(a[1]) && AdjSortedByPopcount(a[1..]))
}

function insert(x: nat, a: seq<nat>): seq<nat>
  decreases |a|
{
  if |a| == 0 then [x]
  else if popcount(x) <= popcount(a[0]) then [x] + a
  else [a[0]] + insert(x, a[1..])
}

function isort(a: seq<nat>): seq<nat>
  decreases |a|
{
  if |a| == 0 then a
  else insert(a[0], isort(a[1..]))
}

lemma lemma_first_insert_head_ge(x: nat, b: seq<nat>, h: nat)
  requires |b| > 0
  requires popcount(h) <= popcount(b[0])
  requires popcount(h) <= popcount(x)
  ensures popcount(h) <= popcount(insert(x, b)[0])
{
  if popcount(x) <= popcount(b[0]) {
    // then insert(x,b) = [x] + b
  } else {
    // then insert(x,b) = [b[0]] + insert(x, b[1..])
  }
}

lemma lemma_insert_len(x: nat, a: seq<nat>)
  ensures |insert(x, a)| == |a| + 1
  decreases |a|
{
  if |a| == 0 {
  } else if popcount(x) <= popcount(a[0]) {
  } else {
    lemma_insert_len(x, a[1..]);
  }
}

lemma lemma_insert_perm_adj(x: nat, a: seq<nat>)
  requires AdjSortedByPopcount(a)
  ensures AdjSortedByPopcount(insert(x, a))
  ensures multiset(insert(x, a)) == multiset(a) + multiset([x])
  decreases |a|
{
  if |a| == 0 {
    // insert(x, []) = [x]
  } else {
    if popcount(x) <= popcount(a[0]) {
      // insert(x, a) = [x] + a
    } else {
      // insert(x, a) = [a[0]] + insert(x, a[1..])
      // adjacency: need head <= first(insert(x, a[1..])) and AdjSorted(insert(...))
      if |a| >= 2 {
        // a[1..] is non-empty
        // From AdjSorted(a), we have popcount(a[0]) <= popcount(a[1])
        assert AdjSortedByPopcount(a[1..]);
        assert popcount(a[0]) <= popcount(a[1]);
        // And popcount(a[0]) <= popcount(x) since else-branch implies popcount(x) > popcount(a[0])
        assert popcount(a[0]) <= popcount(x);
        lemma_insert_perm_adj(x, a[1..]); // establishes AdjSorted(insert(x, a[1..]))
        lemma_first_insert_head_ge(x, a[1..], a[0]);
      } else {
        // a has exactly one element
        // Then insert(x, a[1..]) = insert(x, [])
        // Need popcount(a[0]) <= popcount(x)
        assert popcount(a[0
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
predicate AdjSortedByPopcount(a: seq<nat>)
  decreases |a|
{
  |a| <= 1 || (popcount(a[0]) <= popcount(a[1]) && AdjSortedByPopcount(a[1..]))
}

function insert(x: nat, a: seq<nat>): seq<nat>
  decreases |a|
{
  if |a| == 0 then [x]
  else if popcount(x) <= popcount(a[0]) then [x] + a
  else [a[0]] + insert(x, a[1..])
}

function isort(a: seq<nat>): seq<nat>
  decreases |a|
{
  if |a| == 0 then a
  else insert(a[0], isort(a[1..]))
}

lemma lemma_first_insert_head_ge(x: nat, b: seq<nat>, h: nat)
  requires |b| > 0
  requires popcount(h) <= popcount(b[0])
  requires popcount(h) <= popcount(x)
  ensures popcount(h) <= popcount(insert(x, b)[0])
{
  if popcount(x) <= popcount(b[0]) {
    // then insert(x,b) = [x] + b
  } else {
    // then insert(x,b) = [b[0]] + insert(x, b[1..])
  }
}

lemma lemma_insert_len(x: nat, a: seq<nat>)
  ensures |insert(x, a)| == |a| + 1
  decreases |a|
{
  if |a| == 0 {
  } else if popcount(x) <= popcount(a[0]) {
  } else {
    lemma_insert_len(x, a[1..]);
  }
}

lemma lemma_insert_perm_adj(x: nat, a: seq<nat>)
  requires AdjSortedByPopcount(a)
  ensures AdjSortedByPopcount(insert(x, a))
  ensures multiset(insert(x, a)) == multiset(a) + multiset([x])
  decreases |a|
{
  if |a| == 0 {
    // insert(x, []) = [x]
  } else {
    if popcount(x) <= popcount(a[0]) {
      // insert(x, a) = [x] + a
    } else {
      // insert(x, a) = [a[0]] + insert(x, a[1..])
      // adjacency: need head <= first(insert(x, a[1..])) and AdjSorted(insert(...))
      if |a| >= 2 {
        // a[1..] is non-empty
        // From AdjSorted(a), we have popcount(a[0]) <= popcount(a[1])
        assert AdjSortedByPopcount(a[1..]);
        assert popcount(a[0]) <= popcount(a[1]);
        // And popcount(a[0]) <= popcount(x) since else-branch implies popcount(x) > popcount(a[0])
        assert popcount(a[0]) <= popcount(x);
        lemma_insert_perm_adj(x, a[1..]); // establishes AdjSorted(insert(x, a[1..]))
        lemma_first_insert_head_ge(x, a[1..], a[0]);
      } else {
        // a has exactly one element
        // Then insert(x, a[1..]) = insert(x, [])
        // Need popcount(a[0]) <= popcount(x)
        assert popcount(a[0
// </vc-code>

