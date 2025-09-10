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
lemma lemma_getNextArrivalTimeMonotonic(firstTime: int, interval: int, targetTime1: int, targetTime2: int)
  requires interval > 0
  requires targetTime1 <= targetTime2
  ensures getNextArrivalTime(firstTime, interval, targetTime1) <= getNextArrivalTime(firstTime, interval, targetTime2)
{
}

lemma lemma_div_property(a: int, d: int, k: int)
  requires d > 0
  requires a <= k
  ensures (a + d - 1) / d <= (k + d - 1) / d
{
}

lemma lemma_getNextArrivalTimeProperty(firstTime: int, interval: int, targetTime: int)
  requires interval > 0
  ensures getNextArrivalTime(firstTime, interval, targetTime) >= firstTime
  ensures getNextArrivalTime(firstTime, interval, targetTime) >= targetTime || 
           getNextArrivalTime(firstTime, interval, targetTime) == firstTime
{
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
  var bestIndex := 0;
  var minTime := getNextArrivalTime(routes[0].0, routes[0].1, t);
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant bestIndex >= 0 && bestIndex < n
    invariant minTime == getNextArrivalTime(routes[bestIndex].0, routes[bestIndex].1, t)
    invariant IsOptimalRoute(routes[0..i], t, bestIndex)
  {
    var currentTime := getNextArrivalTime(routes[i].0, routes[i].1, t);
    if currentTime < minTime {
      bestIndex := i;
      minTime := currentTime;
    } else if currentTime == minTime && routes[i].0 < routes[bestIndex].0 {
      bestIndex := i;
      minTime := currentTime;
    }
    i := i + 1;
  }
  
  result := bestIndex + 1;
}
// </vc-code>

