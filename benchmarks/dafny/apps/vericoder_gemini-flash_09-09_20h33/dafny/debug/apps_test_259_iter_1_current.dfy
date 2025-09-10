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
    var minArrivalTime := getNextArrivalTime(routes[0].0, routes[0].1, t);
    var bestRouteIndex := 0;

    var i := 1;
    while i < n
        invariant 0 <= bestRouteIndex < i
        invariant forall k :: 0 <= k < i ==> 
            minArrivalTime <= getNextArrivalTime(routes[k].0, routes[k].1, t)
        invariant minArrivalTime == getNextArrivalTime(routes[bestRouteIndex].0, routes[bestRouteIndex].1, t)
    {
        var currentArrivalTime := getNextArrivalTime(routes[i].0, routes[i].1, t);
        if currentArrivalTime < minArrivalTime {
            minArrivalTime := currentArrivalTime;
            bestRouteIndex := i;
        }
        i := i + 1;
    }

    return bestRouteIndex + 1;
}
// </vc-code>

