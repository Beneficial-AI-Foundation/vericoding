## Task

Generate a sorted list of all possible IP addresses in a network.

For a subnet that is not a valid IPv4 network return `None`.

## Examples
```
ipsubnet2list("192.168.1.0/31") == ["192.168.1.0", "192.168.1.1"]
ipsubnet2list("213.256.46.160/28") == None
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
