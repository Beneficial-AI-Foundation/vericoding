Given n bus routes with start times and intervals, find which route has the earliest bus
arriving at or after target time t. Each route i has first bus at time s_i and subsequent
buses every d_i minutes. Return the 1-indexed route number.

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

method solve(n: int, t: int, routes: seq<(int, int)>) returns (result: int)
  requires ValidInput(n, t, routes)
  ensures 1 <= result <= n
  ensures IsOptimalRoute(routes, t, result - 1)
{
    var ii := 0;
    var tt := getNextArrivalTime(routes[0].0, routes[0].1, t);

    for i := 0 to n
      invariant 0 <= ii < n
      invariant tt == getNextArrivalTime(routes[ii].0, routes[ii].1, t)
      invariant forall j :: 0 <= j < i ==> tt <= getNextArrivalTime(routes[j].0, routes[j].1, t)
    {
        var fr := routes[i].0;
        var d := routes[i].1;

        if fr < t {
            fr := fr + (t - fr + d - 1) / d * d;
        }

        if fr < tt {
            tt := fr;
            ii := i;
        }
    }

    result := ii + 1;
}
