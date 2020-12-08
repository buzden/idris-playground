f : (Int -> Bool) -> Int

il : Int
il = f \x => x > 0

lc : Int
lc = f $ \case 0 => True ; _ => False

ilc : Int
ilc = f \case 0 => True; _ => False
