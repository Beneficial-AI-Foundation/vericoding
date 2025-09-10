predicate ValidCosts(c: array<int>)
  reads c
{
  c.Length == 4 &&
  c[0] >= 1 && c[1] >= 1 && c[2] >= 1 && c[3] >= 1 &&
  c[0] <= 1000 && c[1] <= 1000 && c[2] <= 1000 && c[3] <= 1000
}

predicate ValidRides(rides: array<int>)
  reads rides
{
  rides.Length >= 1 && rides.Length <= 1000 &&
  forall i :: 0 <= i < rides.Length ==> 0 <= rides[i] <= 1000
}

function sum_array(arr: seq<int>): int
  requires forall i :: 0 <= i < |arr| ==> arr[i] >= 0
  ensures sum_array(arr) >= 0
{
  if |arr| == 0 then 0
  else arr[0] + sum_array(arr[1..])
}

function optimized_cost(rides: seq<int>, individual_cost: int, unlimited_cost: int): int
  requires individual_cost >= 1 && unlimited_cost >= 1
  requires forall i :: 0 <= i < |rides| ==> rides[i] >= 0
  ensures optimized_cost(rides, individual_cost, unlimited_cost) >= 0
  ensures optimized_cost(rides, individual_cost, unlimited_cost) <= sum_array(rides) * individual_cost
{
  var initial_cost := sum_array(rides) * individual_cost;
  min_with_unlimited(rides, initial_cost, individual_cost, unlimited_cost, 0)
}

function min_with_unlimited(rides: seq<int>, current_cost: int, individual_cost: int, unlimited_cost: int, index: int): int
  requires index >= 0
  requires individual_cost >= 1 && unlimited_cost >= 1
  requires forall i :: 0 <= i < |rides| ==> rides[i] >= 0
  requires current_cost >= 0
  requires current_cost <= sum_array(rides) * individual_cost
  ensures min_with_unlimited(rides, current_cost, individual_cost, unlimited_cost, index) >= 0
  ensures min_with_unlimited(rides, current_cost, individual_cost, unlimited_cost, index) <= current_cost
  decreases |rides| - index
{
  if index >= |rides| then current_cost
  else 
    var new_cost := current_cost - rides[index] * individual_cost + unlimited_cost;
    var updated_cost := if new_cost < current_cost && new_cost >= 0 then new_cost else current_cost;
    min_with_unlimited(rides, updated_cost, individual_cost, unlimited_cost, index + 1)
}

function CorrectResult(c: array<int>, a: array<int>, b: array<int>, result: int): bool
  reads c, a, b
  requires ValidCosts(c) && ValidRides(a) && ValidRides(b)
{
  result == min5(optimized_cost(a[..], c[0], c[1]) + optimized_cost(b[..], c[0], c[1]),
                 optimized_cost(a[..], c[0], c[1]) + c[2],
                 optimized_cost(b[..], c[0], c[1]) + c[2],
                 c[2] + c[2],
                 c[3])
}

// <vc-helpers>
function min2(x: int, y: int): int
  ensures min2(x, y) <= x
  ensures min2(x, y) <= y
  ensures min2(x, y) == x || min2(x, y) == y
{
  if x <= y then x else y
}

function min5(x1: int, x2: int, x3: int, x4: int, x5: int): int
  ensures min5(x1, x2, x3, x4, x5) <= x1
  ensures min5(x1, x2, x3, x4, x5) <= x2
  ensures min5(x1, x2, x3, x4, x5) <= x3
  ensures min5(x1, x2, x3, x4, x5) <= x4
  ensures min5(x1, x2, x3, x4, x5) <= x5
{
  min2(min2(min2(min2(x1, x2), x3), x4), x5)
}

lemma Min2_glb(z: int, x: int, y: int)
  ensures (z <= x && z <= y) ==> z <= min2(x, y)
{
  if x <= y {
    assert (z <= x && z <= y) ==> z <= x;
  } else {
    assert (z <= x && z <= y) ==> z <= y;
  }
}

lemma Min5_glb(z: int, x1: int, x2: int, x3: int, x4: int, x5: int)
  ensures (z <= x1 && z <= x2 && z <= x3 && z <= x4 && z <= x5) ==> z <= min5(x1, x2, x3, x4, x5)
{
  if z <= x1 && z <= x2 && z <= x3 && z <= x4 && z <= x5 {
    var s1 := min2(x1, x2);
    assert (z <= x1 && z <= x2) ==> z <= s1;
    assert z <= s1;

    var s2 := min2(s1, x3);
    Min2_glb(z, s1, x3);
    assert z <= s2;

    var s3 := min2(s2, x4);
    Min2_glb(z, s2, x4);
    assert z <= s3;

    var s4 := min2(s3, x5);
    Min2_glb(z, s3, x5);
    assert z <= s4;

    assert s4 == min5(x1, x2, x3, x4, x5);
  }
}

lemma Min2_nonneg(x: int, y: int)
  ensures (0 <= x && 0 <= y) ==> 0 <= min2(x, y)
{
  if 0 <= x && 0 <= y {
    if x <= y {
      assert 0 <= x;
    } else {
      assert 0 <= y;
    }
  }
}

lemma Min5_nonneg(x1: int, x2: int, x3: int, x4: int, x5: int)
  ensures (0 <= x1 && 0 <= x2 && 0 <= x3 && 0 <= x4 && 0 <= x5) ==> 0 <= min5(x1, x2, x3, x4, x5)
{
  if 0 <= x1 && 0 <= x2 && 0 <= x3 && 0 <= x4 && 0 <= x5 {
    var s1 := min2(x1, x2);
    Min2_nonneg(x1, x2);
    assert 0 <= s1;

    var s2 := min2(s1, x3);
    Min2_nonneg(s1, x3);
    assert 0 <= s2;

    var s3 := min2(s2, x4);
    Min2_nonneg(s2, x4);
    assert 0 <= s3;

    var s4 := min2(s3, x5);
    Min2_nonneg(s3, x5);
    assert 0 <= s4;

    assert s4 == min5(x1, x2, x3, x4, x5);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(c: array<int>, a: array<int>, b: array<int>) returns (result: int)
  requires ValidCosts(c)
  requires ValidRides(a)
  requires ValidRides(b)
  ensures result >= 0
  ensures CorrectResult(c, a, b, result)
  ensures result <= min5(sum_array(a[..]) * c[0] + sum_array(b[..]) * c[0], 
                        sum_array(a[..]) * c[0] + c[2],
                        sum_array(b[..]) * c[0] + c[2],
                        c[2] + c[2],
                        c[3])
// </vc-spec>
// <vc-code>
{
  var oa := optimized_cost(a[..], c[0], c[1]);
  var ob := optimized_cost(b[..], c[0], c[1]);

  var x1 := oa + ob;
  var x2 := oa + c[2];
  var x3 := ob + c[2];
  var x4 := c[2] + c[2];
  var x5 := c[3];

  result := min5(x1, x2, x3, x4, x5);

  // Non-negativity
  assert oa >= 0;
  assert ob >= 0;
  assert c[2] >= 1 && c[3] >= 1;
  assert x1 >= 0;
  assert x2 >= 0;
  assert x3 >= 0;
  assert x4 >= 0;
  assert x5 >= 0;
  Min5_nonneg(x1, x2, x3, x4, x5);
  assert 0 <= result;

  // CorrectResult equality
  assert CorrectResult(c, a, b, result);

  // Upper-bound via per-argument bounds and GLB lemma
  var sa := sum_array(a[..]);
  var sb := sum_array(b[..]);

  var y1 := sa * c[0] + sb * c[0];
  var y2 := sa * c[0] + c[2];
  var y3 := sb * c[0] + c[2];
  var y4 := c[2] + c[2];
  var y5 := c[3];

  assert oa <= sa * c[0];
  assert ob <= sb * c[0];

  assert x1 <= y1;
  assert x2 <= y2;
  assert x3 <= y3;
  assert x4 <= y4;
  assert x5 <= y5;

  assert result <= x1;
  assert result <= y1;
  assert result <= x2;
  assert result <= y2;
  assert result <= x3;
  assert result <= y3;
  assert result <= x4;
  assert result <= y4;
  assert result <= x5;
  assert result <= y5;

  Min5_glb(result, y1, y2, y3, y4, y5);
  assert result <= min5(y1, y2, y3, y4, y5);
}
// </vc-code>

