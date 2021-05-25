module Data.SortedMap.Extra

import Data.SortedMap
import Data.List

export
filter : Ord k => (k -> v -> Bool) -> SortedMap k v -> SortedMap k v
filter pred = fromList . filter (uncurry pred) . toList

export
size : Foldable t => t a -> Nat
size = foldr (\_ => (+ 1)) 0
