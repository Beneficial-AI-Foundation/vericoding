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
  ensures min2(x, y) <= x && min2(x, y) <= y
  ensures min2(x, y) == x || min2(x, y) == y
{
  if x < y then x else y
}

function min3(x: int, y: int, z: int): int
  ensures min3(x, y, z) <= x && min3(x, y, z) <= y && min3(x, y, z) <= z
  ensures min3(x, y, z) == x || min3(x, y, z) == y || min3(x, y, z) == z
{
  min2(x, min2(y, z))
}

function min4(x: int, y: int, z: int, w: int): int
  ensures min4(x, y, z, w) <= x && min4(x, y, z, w) <= y && min4(x, y, z, w) <= z && min4(x, y, z, w) <= w
  ensures min4(x, y, z, w) == x || min4(x, y, z, w) == y || min4(x, y, z, w) == z || min4(x, y, z, w) == w
{
  min2(x, min3(y, z, w))
}

function min5(x: int, y: int, z: int, w: int, v: int): int
  ensures min5(x,y,z,w,v) <= x && min5(x,y,z,w,v) <= y && min5(x,y,z,w,v) <= z && min5(x,y,z,w,v) <= w && min5(x,y,z,w,v) <= v
  ensures min5(x,y,z,w,v) == x || min5(x,y,z,w,v) == y || min5(x,y,z,w,v) == z || min5(x,y,z,w,v) == w || min5(x,y,z,w,v) == v
{
  min2(x, min4(y, z, w, v))
}

// proof that optimized_cost is non-negative
lemma optimized_cost_non_negative(rides: seq<int>, individual_cost: int, unlimited_cost: int)
  requires individual_cost >= 1 && unlimited_cost >= 1
  requires forall i :: 0 <= i < |rides| ==> rides[i] >= 0
  ensures optimized_cost(rides, individual_cost, unlimited_cost) >= 0
{
  // This is implicitly handled by the function's postcondition.
  // No explicit proof steps are needed here, as it's a direct consequence
  // of how `optimized_cost` and `min_with_unlimited` are defined and their ensures clauses.
}

// proof that sum_array is non-negative
lemma sum_array_non_negative(arr: seq<int>)
  requires forall i :: 0 <= i < |arr| ==> arr[i] >= 0
  ensures sum_array(arr) >= 0
{
  // This is implicitly handled by the function's postcondition.
  // No explicit proof steps are needed here.
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
    var cost_a_individual_per_ride := optimized_cost(a[..], c[0], c[1]);
    var cost_b_individual_per_ride := optimized_cost(b[..], c[0], c[1]);

    var option1 := cost_a_individual_per_ride + cost_b_individual_per_ride;
    var option2 := cost_a_individual_per_ride + c[2];
    var option3 := cost_b_individual_per_ride + c[2];
    var option4 := c[2] + c[2];
    var option5 := c[3];

    result := min5(option1, option2, option3, option4, option5);
    
    // Proof of result >= 0
    // Since c[0] >= 1, c[1] >= 1, c[2] >= 1, c[3] >= 1
    // and rides values are >= 0,
    // optimized_cost always returns a non-negative value.
    // This implies option1, option2, option3 are non-negative.
    // option4 (c[2] + c[2]) is non-negative.
    // option5 (c[3]) is non-negative.
    // Therefore, the minimum of these non-negative values must be non-negative.
    assert option1 >= 0 by {
      optimized_cost_non_negative(a[..], c[0], c[1]);
      optimized_cost_non_negative(b[..], c[0], c[1]);
    }
    assert option2 >= 0 by {
      optimized_cost_non_negative(a[..], c[0], c[1]);
    }
    assert option3 >= 0 by {
      optimized_cost_non_negative(b[..], c[0], c[1]);
    }
    assert option4 >= 0; // c[2] >= 1
    assert option5 >= 0; // c[3] >= 1
    assert result >= 0;
}
// </vc-code>

