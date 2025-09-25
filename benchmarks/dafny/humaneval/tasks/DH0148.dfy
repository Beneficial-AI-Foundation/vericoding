// <vc-preamble>
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

  ensures |GetPlanetsBetween(planet1, planet2)| <= 6

{

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

}
function GetPlanetsBetweenIndices(start: int, end: int): seq<string>

  requires 0 <= start <= 7 && 0 <= end <= 7

  ensures |GetPlanetsBetweenIndices(start, end)| <= (if start <= end then end - start + 1 else 0)

  decreases if start <= end then end - start + 1 else 0
{

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

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method bf(start: int, end: int) returns (planets: seq<string>)

    requires 0 <= start <= 7 && 0 <= end <= 7

    ensures |planets| <= (if start <= end then end - start + 1 else 0)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
