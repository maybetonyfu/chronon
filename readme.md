
(tall(), )


Example from https://www.brainzilla.com
The perf is visited on Monday or Tuesday, not black hair,  

john works is blond, 

brian likes spiderman
tony doesn't like superman


spiderman(brian)
not_superman(tony)
batman(sean)

spiderman(brian)
not_superman(tony)
superman(sean)

spiderman(brian)
not_superman(tony)
spiderman(sean)


-- a child can only choose one superhero
spiderman(x), superman(x) ==> false
spiderman(x), batman(x) ==> false
superman(x), batman(x) ==> false
-- child cannot like and dislike a superhero
spiderman(x), not_spiderman(x) ==> false
superman(x), not_superman(x) ==> false
batman(x), not_batman(x) ==> false
spiderman(x) ==> not_superman(x), not_batman(x)
superman(x) ==> not_spiderman(x), not_batman(x)
batman(x) ==> not_spiderman(x), not_superman(x)
not_superman(x), not_batman(x) <=> spiderman(x)
not_superman(x), not_spiderman(x) <=> batman(x)
not_batman(x), not_spiderman(x) <=> superman(x)
spiderman(x), superman(y), batman(z) <=> true


