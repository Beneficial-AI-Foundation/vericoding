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
  ensures x <= y ==> min2(x, y) == x
  ensures y <= x ==> min2(x, y) == y
  ensures x >= 0 && y >= 0 ==> min2(x, y) >= 0
{
  if x <= y then x else y
}

function min5(a: int, b: int, c: int, d: int, e: int): int
  ensures min5(a, b, c, d, e) <= a
  ensures min5(a, b, c, d, e) <= b
  ensures min5(a, b, c, d, e) <= c
  ensures min5(a, b, c, d, e) <= d
  ensures min5(a, b, c, d, e) <= e
  ensures (a >= 0 && b >= 0 && c >= 0 && d >= 0 && e >= 0) ==> min5(a, b, c, d, e) >= 0
{
  min2(min2(min2(min2(a, b), c), d), e)
}

lemma Min2Glb(z: int, x: int, y: int)
  requires z <= x && z <= y
  ensures z <= min2(x, y)
{
  if x <= y {
    assert min2(x, y) == x;
  } else {
    assert min2(x, y) == y;
  }
}

lemma Min5Monotone(a1: int, b1: int, c1: int, d1: int, e1: int,
                   a2: int, b2: int, c2: int, d2: int, e2: int)
  requires a1 <= a2 && b1 <= b2 && c1 <= c2 && d1 <= d2 && e1 <= e2
  ensures min5(a1, b1, c1, d1, e1) <= min5(a2, b2, c2, d2, e2)
{
  var m1 := min5(a1, b1, c1, d1, e1);
  assert m1 <= a1;
  assert m1 <= b1;
  assert m1 <= c1;
  assert m1 <= d1;
  assert m1 <= e1;

  assert m1 <= a2;
  assert m1 <= b2;
  assert m1 <= c2;
  assert m1 <= d2;
  assert m1 <= e2;

  assert m1 <= min2(a2, b2) by { Min2Glb(m1, a2, b2); }
  assert m1 <= min2(min2(a2, b2), c2) by { Min2Glb(m1, min2(a2, b2), c2); }
  assert m1 <= min2(min2(min2(a2, b2), c2), d2) by { Min2Glb(m1, min2(min2(a2, b2), c2), d2); }
  assert m1 <= min2(min2(min2(min2(a2, b2), c2), d2), e2) by { Min2Glb(m1, min2(min2(min2(a2, b2), c2), d2), e2); }
  assert min5(a2, b2, c2, d2, e2) == min2(min2(min2(min2(a2, b2), c2), d2), e2);
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
  var ocA := optimized_cost(a[..], c[0], c[1]);
  var ocB := optimized_cost(b[..], c[0], c[1]);

  var x1 := ocA + ocB;
  var x2 := ocA + c[2];
  var x3 := ocB + c[2];
  var x4 := c[2] + c[2];
  var x5 := c[3];

  result := min5(x1, x2, x3, x4, x5);

  var y1 := sum_array(a[..]) * c[0] + sum_array(b[..]) * c[0];
  var y2 := sum_array(a[..]) * c[0] + c[2];
  var y3 := sum_array(b[..]) * c[0] + c[2];
  var y4 := c[2] + c[2];
  var y5 := c[3];

  assert ocA >= 0 && ocB >= 0;
  assert c[2] >= 1 && c[3] >= 1;
  assert x1 >= 0 && x2 >= 0 && x3 >= 0 && x4 >= 0 && x5 >= 0;

  assert ocA <= sum_array(a[..]) * c[0];
  assert ocB <= sum_array(b[..]) * c[0];

  assert x1 <= y1;
  assert x2 <= y2;
  assert x3 <= y3;
  assert x4 <= y4;
  assert x5 <= y5;

  Min5Monotone(x1, x2, x3, x4, x5, y1, y2, y3, y4, y5);

  assert result == min5(x1, x2, x3, x4, x5);
  assert min5(x1, x2, x3, x4, x5) <= min5(y1, y2, y3, y4, y5);
  assert result <= min5(y1, y2, y3, y4, y5);
}
// </vc-code>

