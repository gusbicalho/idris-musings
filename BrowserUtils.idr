module BrowserUtils

import Data.IORef

%foreign "browser:lambda: x => console.log(x)"
prim__consoleLog : String -> PrimIO ()

export
consoleLog : (Show a, HasIO io) => a -> io ()
consoleLog x = primIO $ prim__consoleLog (show x)

%foreign "browser:lambda: (collection, callback) => for (item of collection) { callback(item) }"
prim__forEach : AnyPtr -> (AnyPtr -> PrimIO ()) -> PrimIO ()

namespace DOM
  export data DOMNode = MkNode AnyPtr

  %foreign "browser:lambda: (selector) => document.querySelectorAll(selector)"
  prim__querySelectorAll : String -> PrimIO AnyPtr

  querySelectorAll : HasIO io => String -> io (List DOMNode)
  querySelectorAll selector = do
    ref <- IORef.newIORef []
    elements <- primIO (prim__querySelectorAll selector)
    primIO $ prim__forEach elements \e => do
      toPrim $ modifyIORef ref (e ::)
    els <- readIORef ref
    pure $ ?reverse els
