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
lemma OptimalRouteExists(routes: seq<(int, int)>, t: int)
  requires |routes| > 0
  requires forall i :: 0 <= i < |routes| ==> routes[i].1 > 0
  ensures exists k :: 0 <= k < |routes| && IsOptimalRoute(routes, t, k)
{
  var minIndex := 0;
  var minTime := getNextArrivalTime(routes[0].0, routes[0].1, t);
  
  var i := 1;
  while i < |routes|
    invariant 0 <= i <= |routes|
    invariant 0 <= minIndex < |routes|
    invariant minTime == getNextArrivalTime(routes[minIndex].0, routes[minIndex].1, t)
    invariant forall j :: 0 <= j < i ==> minTime <= getNextArrivalTime(routes[j].0, routes[j].1, t)
  {
    var currTime := getNextArrivalTime(routes[i].0, routes[i].1, t);
    if currTime < minTime {
      minIndex := i;
      minTime := currTime;
    }
    i := i + 1;
  }
  
  assert IsOptimalRoute(routes, t, minIndex);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int, routes: seq<(int, int)>) returns (result: int)
  requires ValidInput(n, t, routes)
  ensures 1 <= result <= n
  ensures IsOptimalRoute(routes, t, result - 1)
// </vc-spec>
// <vc-code>
{
  var minIndex := 0;
  var minTime := getNextArrivalTime(routes[0].0, routes[0].1, t);
  
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= minIndex < n
    invariant minIndex < i
    invariant minTime == getNextArrivalTime(routes[minIndex].0, routes[minIndex].1, t)
    invariant forall j :: 0 <= j < i ==> minTime <= getNextArrivalTime(routes[j].0, routes[j].1, t)
  {
    var currTime := getNextArrivalTime(routes[i].0, routes[i].1, t);
    if currTime < minTime {
      minIndex := i;
      minTime := currTime;
    }
    i := i + 1;
  }
  
  result := minIndex + 1;
}
// </vc-code>

