test :: Maybe Bool -> [a] -> Int
test mb as =
  case (mb, as) of
    (mb', as') -> case mb of
      Nothing
        -> case as of
             []
               -> case mb' of
                    Nothing
                      -> case as' of
                           [] -> _
                           (a : as2) -> _
                    (Just b)
                      -> case as' of
                           [] -> _
                           (a : as2) -> _
             (a : as2)
               -> case mb' of
                    Nothing
                      -> case as' of
                           [] -> _
                           (a' : as3) -> _
                    (Just b)
                      -> case as' of
                           [] -> _
                           (a' : as3) -> _
      (Just b)
        -> case as of
             []
               -> case mb' of
                    Nothing
                      -> case as' of
                           [] -> _
                           (a : as2) -> _
                    (Just b')
                      -> case as' of
                           [] -> _
                           (a : as2) -> _
             (a : as2)
               -> case mb' of
                    Nothing
                      -> case as' of
                           [] -> _
                           (a' : as3) -> _
                    (Just b')
                      -> case as' of
                           [] -> _
                           (a' : as3) -> _
