datatype Planet = Mercury | Venus | Earth | Mars | Jupiter | Saturn | Uranus | Neptune
datatype Option<T> = Some(value: T) | None
function PlanetFromString(name: string): Option<Planet>
  ensures PlanetFromString(name).Some? ==> 0 <= PlanetIndex(PlanetFromString(name).value) <= 7
{
  match name
  case "Mercury" => Some(Mercury)
  case "Venus" => Some(Venus)
  case "Earth" => Some(Earth)
  case "Mars" => Some(Mars)
  case "Jupiter" => Some(Jupiter)
  case "Saturn" => Some(Saturn)
  case "Uranus" => Some(Uranus)
  case "Neptune" => Some(Neptune)
  case _ => None
}
function PlanetIndex(p: Planet): int
{
  match p
  case Mercury => 0
  case Venus => 1
  case Earth => 2
  case Mars => 3
  case Jupiter => 4
  case Saturn => 5
  case Uranus => 6
  case Neptune => 7
}
function GetPlanetsBetween(planet1: string, planet2: string): seq<string>
  // post-conditions-start
  ensures |GetPlanetsBetween(planet1, planet2)| <= 6
  // post-conditions-end
{
  // impl-start
  var p1 := PlanetFromString(planet1);
  var p2 := PlanetFromString(planet2);
  if p1.None? || p2.None? then
    []
  else
    var i1 := PlanetIndex(p1.value);
    var i2 := PlanetIndex(p2.value);
    if i1 < i2 then
      GetPlanetsBetweenIndices(i1 + 1, i2 - 1)
    else if i1 > i2 then
      GetPlanetsBetweenIndices(i2 + 1, i1 - 1)
    else
      []
  // impl-end
}
function GetPlanetsBetweenIndices(start: int, end: int): seq<string>
  // pre-conditions-start
  requires 0 <= start <= 7 && 0 <= end <= 7
  // pre-conditions-end
  // post-conditions-start
  ensures |GetPlanetsBetweenIndices(start, end)| <= (if start <= end then end - start + 1 else 0)
  // post-conditions-end
  decreases if start <= end then end - start + 1 else 0
{
  // impl-start
  if start > end then
    []
  else
    match start
    case 0 => ["Mercury"] + GetPlanetsBetweenIndices(1, end)
    case 1 => ["Venus"] + GetPlanetsBetweenIndices(2, end)
    case 2 => ["Earth"] + GetPlanetsBetweenIndices(3, end)
    case 3 => ["Mars"] + GetPlanetsBetweenIndices(4, end)
    case 4 => ["Jupiter"] + GetPlanetsBetweenIndices(5, end)
    case 5 => ["Saturn"] + GetPlanetsBetweenIndices(6, end)
    case 6 => ["Uranus"] + GetPlanetsBetweenIndices(7, end)
    case 7 => ["Neptune"]
  // impl-end
}

// <vc-helpers>
function PlanetFromIndex(index: int): Planet
  requires 0 <= index <= 7
{
  match index
  case 0 => Mercury
  case 1 => Venus
  case 2 => Earth
  case 3 => Mars
  case 4 => Jupiter
  case 5 => Saturn
  case 6 => Uranus
  case 7 => Neptune
}

function PlanetNameFromIndex(index: int): string
  requires 0 <= index <= 7
{
  match index
  case 0 => "Mercury"
  case 1 => "Venus"
  case 2 => "Earth"
  case 3 => "Mars"
  case 4 => "Jupiter"
  case 5 => "Saturn"
  case 6 => "Uranus"
  case 7 => "Neptune"
}
// </vc-helpers>

// <vc-spec>
method bf(start: int, end: int) returns (planets: seq<string>)
    // pre-conditions-start
    requires 0 <= start <= 7 && 0 <= end <= 7
    // pre-conditions-end
    // post-conditions-start
    ensures |planets| <= (if start <= end then end - start + 1 else 0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if start > end then
        planets := [];
    else
        var result: seq<string> := [];
        var i := start;
        while i <= end
            invariant start <= i <= end + 1
            invariant |result| == i - start
            invariant forall k :: start <= k < i ==> result[k - start] == PlanetNameFromIndex(k)
        {
            result := result + [PlanetNameFromIndex(i)];
            i := i + 1;
        }
        planets := result;
    calc {
        |planets|;
        |result|;
        i - start;
        (end + 1) - start;
        end - start + 1;
    }
}
// </vc-code>

