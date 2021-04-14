-- Non-strictly-positive recursion
data La : Type where
  Lam : (La -> La) -> La

app : La -> La -> La
app (Lam f) x = f x

selfApp : La
selfApp = Lam \x => app x x

om : La
om = app selfApp selfApp
