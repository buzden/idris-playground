namespace A

  public export
  data A : Type where
    Mk : (lala : Nat) -> (alal : String) -> A

namespace B

  public export
  data B : Type where
    Mk : (alal : Char) -> B

namespace C

  public export
  data C : Type where
    Mk : (foo : Integer) -> C

a = Mk {alal = "alal", lala = 4}
b = Mk {alal = 'a'}
c = Mk {foo = 5}
