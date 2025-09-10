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
  ensures exists i :: 0 <= i < |routes| && IsOptimalRoute(routes, t, i)
{
  var times := seq(|routes|, i requires 0 <= i < |routes| => getNextArrivalTime(routes[i].0, routes[i].1, t));
  var minTime := times[0];
  var minIndex := 0;
  
  var j := 1;
  while j < |routes|
    invariant 1 <= j <= |routes|
    invariant 0 <= minIndex < j
    invariant minTime == times[minIndex]
    invariant forall k :: 0 <= k < j ==> times[minIndex] <= times[k]
  {
    if times[j] < minTime {
      minTime := times[j];
      minIndex := j;
    }
    j := j + 1;
  }
  
  assert forall k :: 0 <= k < |routes| ==> times[minIndex] <= times[k];
  assert IsOptimalRoute(routes, t, minIndex);
}

lemma FindOptimalHelper(routes: seq<(int, int)>, t: int, currentBest: int, candidate: int)
  requires 0 <= currentBest < |routes|
  requires 0 <= candidate < |routes|
  requires forall i :: 0 <= i < |routes| ==> routes[i].1 > 0
  requires getNextArrivalTime(routes[candidate].0, routes[candidate].1, t) <= 
           getNextArrivalTime(routes[currentBest].0, routes[currentBest].1, t)
  ensures getNextArrivalTime(routes[candidate].0, routes[candidate].1, t) <= 
          getNextArrivalTime(routes[currentBest].0, routes[currentBest].1, t)
{
}

lemma EstablishOptimalRoute(routes: seq<(int, int)>, t: int, bestRoute: int)
  requires 0 <= bestRoute < |routes|
  requires forall i :: 0 <= i < |routes| ==> routes[i].1 > 0
  requires forall j :: 0 <= j < |routes| ==> 
    getNextArrivalTime(routes[bestRoute].0, routes[bestRoute].1, t) <= 
    getNextArrivalTime(routes[j].0, routes[j].1, t)
  ensures IsOptimalRoute(routes, t, bestRoute)
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
  var bestRoute := 0;
  var bestTime := getNextArrivalTime(routes[0].0, routes[0].1, t);
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= bestRoute < i
    invariant bestTime == getNextArrivalTime(routes[bestRoute].0, routes[bestRoute].1, t)
    invariant forall j :: 0 <= j < i ==> 
      getNextArrivalTime(routes[bestRoute].0, routes[bestRoute].1, t) <= 
      getNextArrivalTime(routes[j].0, routes[j].1, t)
  {
    var currentTime := getNextArrivalTime(routes[i].0, routes[i].1, t);
    if currentTime < bestTime {
      bestRoute := i;
      bestTime := currentTime;
    }
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < n ==> 
    getNextArrivalTime(routes[bestRoute].0, routes[bestRoute].1, t) <= 
    getNextArrivalTime(routes[j].0, routes[j].1, t);
  
  EstablishOptimalRoute(routes, t, bestRoute);
  assert IsOptimalRoute(routes, t, bestRoute);
  
  result := bestRoute + 1;
}
// </vc-code>

