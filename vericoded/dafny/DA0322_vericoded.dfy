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
function min5(a: int, b: int, c: int, d: int, e: int): int
  ensures min5(a, b, c, d, e) <= a
  ensures min5(a, b, c, d, e) <= b
  ensures min5(a, b, c, d, e) <= c
  ensures min5(a, b, c, d, e) <= d
  ensures min5(a, b, c, d, e) <= e
  ensures min5(a, b, c, d, e) == a || min5(a, b, c, d, e) == b || 
          min5(a, b, c, d, e) == c || min5(a, b, c, d, e) == d || 
          min5(a, b, c, d, e) == e
{
  if a <= b && a <= c && a <= d && a <= e then a
  else if b <= c && b <= d && b <= e then b
  else if c <= d && c <= e then c
  else if d <= e then d
  else e
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
  // Calculate optimal cost for route A (individual tickets vs unlimited)
  var costA := optimized_cost(a[..], c[0], c[1]);
  
  // Calculate optimal cost for route B (individual tickets vs unlimited)
  var costB := optimized_cost(b[..], c[0], c[1]);
  
  // Option 1: Optimal for A + Optimal for B
  var option1 := costA + costB;
  
  // Option 2: Optimal for A + Unlimited for B
  var option2 := costA + c[2];
  
  // Option 3: Unlimited for A + Optimal for B
  var option3 := c[2] + costB;
  
  // Option 4: Unlimited for both A and B separately
  var option4 := c[2] + c[2];
  
  // Option 5: Combined unlimited for both A and B
  var option5 := c[3];
  
  // Return the minimum of all options
  result := min5(option1, option2, option3, option4, option5);
}
// </vc-code>

