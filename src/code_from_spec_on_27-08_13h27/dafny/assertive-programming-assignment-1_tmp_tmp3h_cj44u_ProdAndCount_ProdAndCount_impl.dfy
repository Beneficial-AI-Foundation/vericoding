function RecursivePositiveProduct(q: seq<int>): int
    decreases |q|
{
    if q == [] then 1
    else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
    else q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
    decreases |q|
{
    if q == [] then 0
    else if q[|q|-1] == key then 1+RecursiveCount(key, q[..|q|-1])
    else RecursiveCount(key, q[..|q|-1])
}

function county(elem: int, key: int): int{
    if elem==key then 1 else 0
}

function prody(elem: int): int{
    if elem <= 0 then 1 else elem
}

// <vc-helpers>
lemma ProductAndCountCorrect(q: seq<int>, key: int, prodAcc: int, countAcc: nat)
  requires prodAcc == RecursivePositiveProduct(q)
  requires countAcc == RecursiveCount(key, q)
  ensures prodAcc == RecursivePositiveProduct(q)
  ensures countAcc == RecursiveCount(key, q)
{
}

lemma ProductSplit(q: seq<int>, i: int)
  requires 0 <= i <= |q|
  ensures RecursivePositiveProduct(q[..i]) * RecursivePositiveProduct(q[i..]) == RecursivePositiveProduct(q)
{
  if i == 0 {
    assert q[..i] == [];
    assert q[i..] == q;
    assert RecursivePositiveProduct(q[..i]) == 1;
    assert RecursivePositiveProduct(q[..i]) * RecursivePositiveProduct(q[i..]) == RecursivePositiveProduct(q);
  } else if i == |q| {
    assert q[i..] == [];
    assert q[..i] == q;
    assert RecursivePositiveProduct(q[i..]) == 1;
    assert RecursivePositiveProduct(q[..i]) * RecursivePositiveProduct(q[i..]) == RecursivePositiveProduct(q);
  } else {
    assert q[..i] + q[i..] == q;
    if q[0] <= 0 {
      calc {
        RecursivePositiveProduct(q);
        RecursivePositiveProduct(q[1..]);
        { ProductSplit(q[1..], i-1); }
        RecursivePositiveProduct(q[1..][..i-1]) * RecursivePositiveProduct(q[1..][i-1..]);
        { assert q[1..][..i-1] == q[1..i]; }
        { assert q[1..][i-1..] == q[i..]; }
        RecursivePositiveProduct(q[1..i]) * RecursivePositiveProduct(q[i..]);
        { assert q[..i] == q[0..i]; }
        RecursivePositiveProduct(q[..i]) * RecursivePositiveProduct(q[i..]);
      }
    } else {
      calc {
        RecursivePositiveProduct(q);
        q[0] * RecursivePositiveProduct(q[1..]);
        { ProductSplit(q[1..], i-1); }
        q[0] * (RecursivePositiveProduct(q[1..][..i-1]) * RecursivePositiveProduct(q[1..][i-1..]));
        { assert q[1..][..i-1] == q[1..i]; }
        { assert q[1..][i-1..] == q[i..]; }
        q[0] * (RecursivePositiveProduct(q[1..i]) * RecursivePositiveProduct(q[i..]));
        { assert q[..i] == q[0..i]; }
        RecursivePositiveProduct(q[..i]) * RecursivePositiveProduct(q[i..]);
      }
    }
  }
}

lemma CountSplit(q: seq<int>, key: int, i: int)
  requires 0 <= i <= |q|
  ensures RecursiveCount(key, q[..i]) + RecursiveCount(key, q[i..]) == RecursiveCount(key, q)
{
  if i == 0 {
    assert q[..i] == [];
    assert q[i..] == q;
    assert RecursiveCount(key, q[..i]) == 0;
    assert RecursiveCount(key, q[..i]) + RecursiveCount(key, q[i..]) == RecursiveCount(key, q);
  } else if i == |q| {
    assert q[i..] == [];
    assert q[..i] == q;
    assert RecursiveCount(key, q[i..]) == 0;
    assert RecursiveCount(key, q[..i]) + RecursiveCount(key, q[i..]) == RecursiveCount(key, q);
  } else {
    assert q[..i] + q[i..] == q;
    calc {
      RecursiveCount(key, q);
      RecursiveCount(key, q[..i] + q[i..]);
      { assert (q[..i] + q[i..])[..|q[..i]|] == q[..i]; }
      { assert (q[..i] + q[i..])[|q[..i]|..] == q[i..]; }
      RecursiveCount(key, q[..i]) + RecursiveCount(key, q[i..]);
    }
  }
}

lemma ProductUpdate(q: seq<int>, i: int)
  requires 0 <= i < |q|
  ensures RecursivePositiveProduct(q[..i+1]) == RecursivePositiveProduct(q[..i]) * (if q[i] > 0 then q[i] else 1)
{
  calc {
    RecursivePositiveProduct(q[..i+1]);
    { assert q[..i+1] == q[..i] + [q[i]]; }
    RecursivePositiveProduct(q[..i] + [q[i]]);
    { if q[i] <= 0 {
        assert RecursivePositiveProduct([q[i]]) == 1;
      } else {
        assert RecursivePositiveProduct([q[i]]) == q[i];
      } }
    RecursivePositiveProduct(q[..i]) * RecursivePositiveProduct([q[i]]);
    RecursivePositiveProduct(q[..i]) * (if q[i] > 0 then q[i] else 1);
  }
}

lemma CountUpdate(q: seq<int>, key: int, i: int)
  requires 0 <= i < |q|
  ensures RecursiveCount(key, q[..i+1]) == RecursiveCount(key, q[..i]) + (if q[i] == key then 1 else 0)
{
  calc {
    RecursiveCount(key, q[..i+1]);
    { assert q[..i+1] == q[..i] + [q[i]]; }
    RecursiveCount(key, q[..i] + [q[i]]);
    { assert (q[..i] + [q[i]])[..|q[..i]|] == q[..i]; }
    { assert (q[..i] + [q[i]])[|q[..i]|..] == [q[i]]; }
    RecursiveCount(key, q[..i]) + RecursiveCount(key, [q[i]]);
    { if q[i] == key {
        assert RecursiveCount(key, [q[i]]) == 1;
      } else {
        assert RecursiveCount(key, [q[i]]) == 0;
      } }
    RecursiveCount(key, q[..i]) + (if q[i] == key then 1 else 0);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
    ensures prod == RecursivePositiveProduct(q)
    ensures count == RecursiveCount(key, q)
// </vc-spec>
// </vc-spec>

// <vc-code>
method ProdAndCountImpl(q: seq<int>, key: int) returns (prod: int, count: nat)
  ensures prod == RecursivePositiveProduct(q)
  ensures count == RecursiveCount(key, q)
{
  prod := 1;
  count := 0;
  var i := 0;
  while i < |q|
    invariant 0 <= i <= |q|
    invariant prod == RecursivePositiveProduct(q[..i])
    invariant count == RecursiveCount(key, q[..i])
  {
    if q[i] > 0 {
      prod := prod * q[i];
    }
    if q[i] == key {
      count := count + 1;
    }
    i := i + 1;
    if i <= |q| {
      ProductUpdate(q, i-1);
      CountUpdate(q, key, i-1);
    }
  }
  assert i == |q|;
  assert prod == RecursivePositiveProduct(q[..i]);
  assert count == RecursiveCount(key, q[..i]);
  assert q[..i] == q;
}
// </vc-code>
