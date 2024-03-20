--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import Data.Monoid (mappend)
import Hakyll
import System.Process
--------------------------------------------------------------------------------
config :: Configuration
config = defaultConfiguration
  { destinationDirectory = "docs"
  }

coqdocCompiler :: Compiler (Item String)
coqdocCompiler = do
  coq_filename <- toFilePath <$> getUnderlying
  body <- unsafeCompiler $
    readProcess "coqdoc" [ "--no-index"
                         , "--stdout"
                         , "--body-only"
                         , "--parse-comments"
                         , "-utf8"
                         , "-s"
                         , coq_filename ] ""
  makeItem body

main :: IO ()
main = hakyllWith config $ do
  match "images/*" $ do
    route   idRoute
    compile copyFileCompiler

  match "css/*" $ do
    route   idRoute
    compile compressCssCompiler

  -- match "rsc/*" $ do
  --   route   idRoute
  --   compile copyFileCompiler

  match "rsc/*.v" $ do
    route $ setExtension "html"
    compile $ coqdocCompiler
      >>= loadAndApplyTemplate "templates/coqdoc.html" defaultContext
      >>= relativizeUrls

  match "posts/*" $ do
    route $ setExtension "html"
    compile $ pandocCompiler
      >>= loadAndApplyTemplate "templates/post.html"    postCtx
      >>= loadAndApplyTemplate "templates/default.html" postCtx
      >>= relativizeUrls

  create ["archive.html"] $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let archiveCtx =
            listField "posts" postCtx (return posts) `mappend`
            constField "title" "Archives"            `mappend`
            defaultContext

      makeItem ""
        >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
        >>= loadAndApplyTemplate "templates/default.html" archiveCtx
        >>= relativizeUrls

  match "index.html" $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      rscs <- loadAll "rsc/*"
      let indexCtx =
            listField "posts" postCtx (return posts)       `mappend`
            listField "rscs"  defaultContext (return rscs) `mappend`
            defaultContext

      getResourceBody
        >>= applyAsTemplate indexCtx
        >>= loadAndApplyTemplate "templates/default.html" indexCtx
        >>= relativizeUrls

  match "templates/*" $ compile templateBodyCompiler

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%e %B, %Y" `mappend`
    defaultContext
--------------------------------------------------------------------------------
