// see pdf 'ex6 & 7 documentation' for excercise question


datatype Bases = A | C | G | T

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  assume{:axiom} false;
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}

// <vc-helpers>
method Repeat(b: Bases, n: nat) returns (res: seq<Bases>)
  ensures |res| == n
  ensures forall i :: 0 <= i < |res| ==> res[i] == b
  ensures multiset(res)[b] == n
  ensures (forall bb :: bb != b ==> multiset(res)[bb] == 0)
{
  var r: seq<Bases> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> r[j] == b
    invariant multiset(r)[b] == i
    invariant (forall bb :: bb != b ==> multiset(r)[bb] == 0)
  {
    r := r + [b];
    i := i + 1;
  }
  res := r;
}

lemma ConstSeqBordered(s: seq<Bases>, x: Bases)
  requires forall i :: 0 <= i < |s| ==> s[i] == x
  ensures bordered(s)
{
  forall p, q | 0 <= p < |s| && 0 <= q < |s| && p < q
  {
    assert s[p] == x;
    assert s[q] == x;
    assert below(x, x);
  }
}

lemma BorderedAppendConst(left: seq<Bases>, right: seq<Bases>, y: Bases)
  requires bordered(left)
  requires forall j :: 0 <= j < |right| ==> right[j] == y
  requires forall i :: 0 <= i < |left| ==> below(left[i], y)
  ensures bordered(left + right)
{
  forall p, q | 0 <= p < |left + right| && 0 <= q < |left + right| && p < q
  {
    if q < |left| {
      // both in left
      assert 0 <= p < |left|;
      assert 0 <= q < |left|;
      assert below(left[p], left[q]);
    } else if p >= |left| {
      // both in right
      assert 0 <= p - |left| < |right|;
      assert 0 <= q - |left| < |right|;
      assert below(right[p - |left|], right[q - |left|]);
    } else {
      // p in left, q in right
      assert 0 <= p < |left|;
      assert 0 <= q - |left| < |right|;
      assert below(left[p], y);
      assert right[q - |left| ] == y;
      // so below(left[p], right[q-|left|]) since right[...] == y
      assert below(left[p], right[q - |left|]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
// </vc-spec>
// <vc-code>
{
  var aCount := multiset(bases)[A];
  var cCount := multiset(bases)[C];
  var gCount := multiset(bases)[G];
  var tCount := multiset(bases)[T];

  var sa := Repeat(A, aCount);
  var sc := Repeat(C, cCount);
  var sg := Repeat(G, gCount);
  var st := Repeat(T, tCount);

  // sa + sc is bordered
  call ConstSeqBordered(sa, A);
  // prove all elements of sa are below C
  forall i | 0 <= i < |sa|
  {
    assert sa[i] == A;
    assert below(A, C);
  }
  call BorderedAppendConst(sa, sc, C);
  var sac := sa + sc;

  // sac + sg is bordered: prove all elements of sac are <= G
  forall p | 0 <= p < |sac|
  {
    if p < |sa| {
      assert sac[p] == sa[p];
      assert sa[p] == A;
      assert below(A, G);
    } else {
      assert sac[p] == sc[p - |sa|];
      assert sc[p - |sa|] == C;
      assert below(C, G) || below(C, G); // to help instantiation (trivial)
      assert below(C, G);
    }
  };

  call ConstSeqBordered(sg, G);
  call BorderedAppendConst(sac, sg, G);
  var sacg := sac + sg;

  // sacg + st is bordered: prove all elements of sacg are <= T
  forall p | 0 <= p < |sacg|
  {
    if p < |sac| {
      assert sacg[p] == sac[p];
      if p < |sa| {
        assert sac[p] == sa[p];
        assert sa[p] == A;
        assert below(A, T);
      } else {
        assert sac[p] == sc[p - |sa|];
        assert sc[p - |sa|] == C;
        assert below(C, T);
      }
    } else {
      assert sacg[p] == sg[p - |sac|];
      assert sg[p - |sac|] == G;
      assert below(G, T);
    }
  };

  call ConstSeqBordered(st, T);
  call BorderedAppendConst(sacg, st, T);

  sobases := sa + sc + sg + st;

  // multiset equality: counts align by construction
  // show for each base the counts match by case analysis on the base
  forall b | true
  {
    if b == A {
      // only sa contributes A
      assert multiset(sa)[A] == aCount;
      assert multiset(sc)[A] == 0;
      assert multiset(sg)[A] == 0;
      assert multiset(st)[A] == 0;
      assert multiset(sobases)[A] == multiset(sa)[A] + multiset(sc)[A] + multiset(sg)[A] + multiset(st)[A];
      assert multiset(sobases)[A] == aCount;
      assert multiset(sobases)[b] == multiset(bases)[b];
    } else if b == C {
      assert multiset(sa)[C] == 0;
      assert multiset(sc)[C] == cCount;
      assert multiset(sg)[C] == 0;
      assert multiset(st)[C] == 0;
      assert multiset(sobases)[C] == multiset(sa)[C] + multiset(sc)[C] + multiset(sg)[C] + multiset(st)[C];
      assert multiset(sobases)[C] == cCount;
      assert multiset(sobases)[b] == multiset(bases)[b];
    } else if b == G {
      assert multiset(sa)[G] == 0;
      assert multiset(sc)[G] == 0;
      assert multiset(sg)[G] == gCount;
      assert multiset(st)[G] == 0;
      assert multiset(sobases)[G] == multiset(sa)[G] + multiset(sc)[G] + multiset(sg)[G] + multiset(st)[G];
      assert multiset(sobases)[G] == gCount;
      assert multiset(sobases)[b] == multiset(bases)[b];
    } else {
      // b == T
      assert multiset(sa)[T] == 0;
      assert multiset(sc)[T] == 0;
      assert multiset(sg)[T] == 0;
      assert multiset(st)[T] == tCount;
      assert multiset(sobases)[T] == multiset(sa)[T] + multiset(sc)[T] + multiset(sg)[T] + multiset(st)[T];
      assert multiset(sobases)[T] == tCount;
      assert multiset(sobases)[b] == multiset(bases)[b];
    }
  };
}
// </vc-code>

