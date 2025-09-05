Convert DD (decimal degrees) position to DMS (degrees, minutes, seconds).

##### Inputs:
`dd_lat` and `dd_lon` 2 strings representing the latitude and the longitude in degree -i.e. 2 floats included in [-90, 90] and [-180, 180]. Note that latitude 0 is north, longitude 0 is east.

##### Outputs:
A tuple of DMS latitudes formated as follows:
`DDD*mm'ss.sss"C`

With:
- `DDD`: degrees
- `mm`: minutes
- `ss.sss`: seconds rounded to 3 decimals
- `C`: first letter uppercase of the cardinal direction

##### ressources
about WGS 84 on [Wikipedia](https://en.wikipedia.org/wiki/World_Geodetic_System#WGS84)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
