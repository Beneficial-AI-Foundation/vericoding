You must create a method that can convert a string from any format into CamelCase. This must support symbols too.

*Don't presume the separators too much or you could be surprised.*

### Tests
```python
camelize("example name")   # => ExampleName
camelize("your-NaMe-here") # => YourNameHere
camelize("testing ABC")    # => TestingAbc
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded