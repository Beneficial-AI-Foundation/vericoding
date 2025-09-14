predicate ValidInput(n: int, t: int, routes: seq<(int, int)>)
{
  n > 0 && |routes| == n && 
  forall i :: 0 <= i < n ==> routes[i].1 > 0
}

function getNextArrivalTime(firstTime: int, interval: int, targetTime: int): int
  requires interval > 0
{
  if firstTime >= targetTime then firstTime
  else firstTime + ((targetTime - firstTime + interval - 1) / interval) * interval
}

predicate IsOptimalRoute(routes: seq<(int, int)>, t: int, routeIndex: int)
  requires 0 <= routeIndex < |routes|
  requires forall i :: 0 <= i < |routes| ==> routes[i].1 > 0
{
  forall i :: 0 <= i < |routes| ==> 
    getNextArrivalTime(routes[routeIndex].0, routes[routeIndex].1, t) <= 
    getNextArrivalTime(routes[i].0, routes[i].1, t)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int, routes: seq<(int, int)>) returns (result: int)
  requires ValidInput(n, t, routes)
  ensures 1 <= result <= n
  ensures IsOptimalRoute(routes, t, result - 1)
// </vc-spec>
// <vc-code>
{
  var best := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant n == |routes|
    invariant forall k :: 0 <= k < |routes| ==> routes[k].1 > 0
    invariant 0 <= best < i
    invariant forall j :: 0 <= j < i ==>
      getNextArrivalTime(routes[best].0, routes[best].1, t) <=
      getNextArrivalTime(routes[j].0, routes[j].1, t)
    decreases n - i
  {
    if getNextArrivalTime(routes[i].0, routes[i].1, t) <
       getNextArrivalTime(routes[best].0, routes[best].1, t) {
      best := i;
    }
    i := i + 1;
  }
  result := best + 1;
}
// </vc-code>

