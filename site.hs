--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import Data.Monoid     (mappend)
import Hakyll
import Data.List       (stripPrefix)
import System.Process
import System.FilePath (takeBaseName, (</>))
--------------------------------------------------------------------------------
config :: Configuration
config = defaultConfiguration
  { destinationDirectory = "docs"
  }

coqdocCompiler :: Compiler (Item String)
coqdocCompiler = do
  coqFilename <- toFilePath <$> getUnderlying
  body <- unsafeCompiler $
    readProcess "coqdoc" [ "--no-index"
                         , "--stdout"
                         , "--body-only"
                         , "--parse-comments"
                         , "-utf8"
                         , "-s"
                         , coqFilename ] ""
  makeItem body

coqPostCompiler :: Compiler (Item String)
coqPostCompiler = do
  id <- getUnderlying
  route <- getRoute id
  coqFilename <- getMetadataField id "coqfile"
  case coqFilename of
    Just coqFilename ->
      let fullName = "rsc" </> coqFilename
          baseName = takeBaseName coqFilename in do
        postBody <- loadBody $ fromFilePath fullName
        makeItem $ flip withUrls postBody $ \url ->
          case (stripPrefix (baseName ++ ".html") url, route) of
            (Just url', Just route) -> toUrl $ route ++ url'
            _ -> url
    Nothing -> error "Missing metadata \"coqfile\""
--------------------------------------------------------------------------------
main :: IO ()
main = hakyllWith config $ do
  match "images/*" $ do
    route   idRoute
    compile copyFileCompiler

  match "css/*" $ do
    route   idRoute
    compile compressCssCompiler

  match "rsc/*.v" $ do
    compile $ coqdocCompiler

  match "posts/*.coqpost" $ do
    route $ setExtension "html"
    compile $ coqPostCompiler
      >>= loadAndApplyTemplate "templates/coqdoc.html" defaultContext
      >>= relativizeUrls

  -- match "posts/*" $ do
  --   route $ setExtension "html"
  --   compile $ pandocCompiler
  --     >>= loadAndApplyTemplate "templates/post.html"    postCtx
  --     >>= loadAndApplyTemplate "templates/default.html" postCtx
  --     >>= relativizeUrls

  -- create ["archive.html"] $ do
  --   route idRoute
  --   compile $ do
  --     posts <- recentFirst =<< loadAll "posts/*"
  --     let archiveCtx =
  --           listField "posts" postCtx (return posts) `mappend`
  --           constField "title" "Archives"            `mappend`
  --           defaultContext

  --     makeItem ""
  --       >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
  --       >>= loadAndApplyTemplate "templates/default.html" archiveCtx
  --       >>= relativizeUrls

  match "index.html" $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let indexCtx =
            listField "posts" postCtx (return posts)       `mappend`
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
