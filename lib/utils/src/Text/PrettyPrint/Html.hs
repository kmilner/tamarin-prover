{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Pretty-printing with support for HTML markup and proper HTML escaping.
module Text.PrettyPrint.Html (
  -- * HtmlDocument class
    HtmlDocument(..)

  , withTag
  , withTagNonEmpty
  , closedTag

  , module Text.PrettyPrint.Highlight

  -- * HtmlDoc: adding HTML markup
  , HtmlDoc
  , htmlDoc
  , getHtmlDoc
  , DotHtmlDoc
  , postprocessHtmlDoc
  , renderHtmlDoc
  , renderDotHtmlDoc
  , renderDotHtmlDocStyle

  -- * NoHtmlDoc: ignoring HTML markup
  , noHtmlDoc
  , getNoHtmlDoc
  ) where

import Data.Char (isSpace)
-- import Data.Traversable (sequenceA)
import Data.Monoid

import Control.Arrow (first)
import Control.Applicative
import Control.Monad.Identity
import Control.DeepSeq

import Text.PrettyPrint.Class
import Text.PrettyPrint.Highlight

------------------------------------------------------------------------------
-- HtmlDocument class
------------------------------------------------------------------------------


class HighlightDocument d => HtmlDocument d where
    -- | @unescapedText str@ converts the 'String' @str@ to a document without
    -- performing any escaping.
    unescapedText :: String -> d

    -- | @unescapedZeroWidthText str@ converts the 'String' @str@ to a document
    -- with zero width without performing any escaping.
    unescapedZeroWidthText :: String -> d

-- | @withTag tag attrs inner@ adds the tag @tag@ with the attributes
-- @attrs@ around the @inner@ document.
withTag :: HtmlDocument d => String -> [(String,String)] -> d -> d
withTag tag attrs inner =
    unescapedZeroWidthText open <> inner <> unescapedZeroWidthText close
  where
    open  = "<" ++ tag ++ concatMap attribute attrs ++ ">"
    close = "</" ++ tag ++ ">"

-- | @closedTag tag attrs@ builds the closed tag @tag@ with the attributes
-- @attrs@; e.g.,
--
-- > closedTag "img" "href" "here" = HtmlDoc (text "<img href=\"here\"/>)
--
closedTag :: HtmlDocument d => String -> [(String,String)] -> d
closedTag tag attrs = 
    unescapedZeroWidthText $ "<" ++ tag ++ concatMap attribute attrs ++ "/>"

-- | @withTagNonEmpty tag attrs inner@ adds the tag @tag@ with the attributes
-- @attrs@ around the @inner@ document iff @inner@ is a non-empty document.
withTagNonEmpty :: HtmlDocument d => String -> [(String,String)] -> d -> d
withTagNonEmpty tag attrs inner =
    caseEmptyDoc inner emptyDoc $ withTag tag attrs inner

-- | Render an attribute.
attribute :: (String, String) -> String
attribute (key,value) = " " ++ key ++ "=\"" ++ escapeHtmlString value ++ "\""


------------------------------------------------------------------------------
-- HtmlDoc: adding HTML markup
------------------------------------------------------------------------------

-- | A 'Document' transformer that adds proper HTML escaping.
newtype HtmlDoc d = HtmlDoc { getHtmlDoc :: d }
    deriving( Monoid )

-- | Wrap a document such that HTML markup can be added without disturbing the
-- layout.
htmlDoc :: d -> HtmlDoc d
htmlDoc = HtmlDoc

instance NFData d => NFData (HtmlDoc d) where
    rnf = rnf . getHtmlDoc

instance Document d => Document (HtmlDoc d) where
    char          = HtmlDoc . escapeHtmlEntities . return
    text          = HtmlDoc . escapeHtmlEntities
    zeroWidthText = HtmlDoc . zeroWidthText . escapeHtmlString

    HtmlDoc d1 <-> HtmlDoc d2 = HtmlDoc $ d1 <-> d2
    hcat = HtmlDoc . hcat . map getHtmlDoc
    hsep = HtmlDoc . hsep . map getHtmlDoc

    HtmlDoc d1 $$  HtmlDoc d2 = HtmlDoc $ d1 $$ d2
    HtmlDoc d1 $-$ HtmlDoc d2 = HtmlDoc $ d1 $-$ d2
    vcat = HtmlDoc . vcat . map getHtmlDoc

    sep = HtmlDoc . sep . map getHtmlDoc
    cat = HtmlDoc . cat . map getHtmlDoc

    fsep = HtmlDoc . fsep . map getHtmlDoc
    fcat = HtmlDoc . fcat . map getHtmlDoc

    nest i = HtmlDoc . nest i . getHtmlDoc
    caseEmptyDoc (HtmlDoc d1) (HtmlDoc d2) (HtmlDoc d3) = 
        HtmlDoc $ caseEmptyDoc d1 d2 d3

instance Document d => HtmlDocument (HtmlDoc d) where
    unescapedText = HtmlDoc . text
    unescapedZeroWidthText = HtmlDoc . zeroWidthText

instance Document d => HighlightDocument (HtmlDoc d) where
    highlight hlStyle
        | hlStyle == SpecialTerm  = withTag "font" [("color", "#0000CD")]
        | otherwise               = withTag "span" [("class", hlClass hlStyle)]
      where
        hlClass Comment  = "hl_comment"
        hlClass Keyword  = "hl_keyword"
        hlClass Operator = "hl_operator"
        hlClass _        = ""

-- | A 'Document' transformer that inherits from html documents but does not apply
-- html tags that are not in the graphviz spec
newtype DotHtmlDoc d = DotHtmlDoc (HtmlDoc d)
    deriving( Monoid, NFData, Document, HtmlDocument )

instance Document d => HighlightDocument (DotHtmlDoc d) where
    highlight hlStyle (DotHtmlDoc doc)
        | hlStyle == SpecialTerm  = DotHtmlDoc (withTag "font" [("color", "#0000CD")] doc)
        | otherwise               = DotHtmlDoc doc

-- | Escape HTML entities in a string
-- Converts to a document to preserve sizing
escapeHtmlEntities :: Document d
                   => String     -- ^ String to escape
                   -> d          -- ^ Resulting document
escapeHtmlEntities []     = text ""
escapeHtmlEntities (c:cs) = case c of
    '<'  -> text "&" <> zeroWidthText "lt;"   <> escapeHtmlEntities cs
    '>'  -> text "&" <> zeroWidthText "gt;"   <> escapeHtmlEntities cs
    '&'  -> text "&" <> zeroWidthText "amp;"  <> escapeHtmlEntities cs
    '"'  -> text "&" <> zeroWidthText "quot;" <> escapeHtmlEntities cs
    '\'' -> text "&" <> zeroWidthText "#39;"  <> escapeHtmlEntities cs
    x    -> char x <> escapeHtmlEntities cs


-- | Escape HTML entities in a string
--
-- Copied from 'blaze-html'.
escapeHtmlString :: String  -- ^ String to escape
                 -> String  -- ^ Resulting string
escapeHtmlString []     = []
escapeHtmlString (c:cs) = case c of
    '<'  -> "&lt;"   ++ escapeHtmlString cs
    '>'  -> "&gt;"   ++ escapeHtmlString cs
    '&'  -> "&amp;"  ++ escapeHtmlString cs
    '"'  -> "&quot;" ++ escapeHtmlString cs
    '\'' -> "&#39;"  ++ escapeHtmlString cs
    x    -> x : escapeHtmlString cs

-- | @renderHtmlDoc = 'postprocessHtmlDoc' . 'render' . 'getHtmlDoc'@ 
renderHtmlDoc :: HtmlDoc Doc -> String
renderHtmlDoc = postprocessHtmlDoc . render . getHtmlDoc

renderDotHtmlDoc :: DotHtmlDoc Doc -> String
renderDotHtmlDoc (DotHtmlDoc d) = postprocessDotHtmlDoc $ render $ getHtmlDoc d

renderDotHtmlDocStyle :: Style -> DotHtmlDoc Doc -> String
renderDotHtmlDocStyle s (DotHtmlDoc d) = postprocessDotHtmlDoc $ renderStyle s $ getHtmlDoc d

-- | @postprocessHtmlDoc cs@ converts the line-breaks of @cs@ to @<br>@ tags and
-- the prefixed spaces in every line of @cs@ by non-breaing HTML spaces @&nbsp;@.
postprocessHtmlDoc :: String -> String
postprocessHtmlDoc = 
    unlines . map (addBreak . indent) . lines
  where
    addBreak = (++"<br/>")
    indent   = uncurry (++) . (first $ concatMap (const "&nbsp;")) . span isSpace

postprocessDotHtmlDoc :: String -> String
postprocessDotHtmlDoc =
    unlines . map (indent) . lines
  where
--    addBreak = (++"<br/>")
    indent   = uncurry (++) . (first $ concatMap (const " ")) . span isSpace

------------------------------------------------------------------------------
-- NoHtmlDoc: ignoring HTML markup
------------------------------------------------------------------------------

-- | A 'Document' transformer that ignores all 'HtmlDocument' specific methods.
newtype NoHtmlDoc d = NoHtmlDoc { unNoHtmlDoc :: Identity d }
  deriving( Functor, Applicative )


-- | Wrap a document such that all 'HtmlDocument' specific methods are ignored.
noHtmlDoc :: d -> NoHtmlDoc d
noHtmlDoc = NoHtmlDoc . Identity

-- | Extract the wrapped document.
getNoHtmlDoc :: NoHtmlDoc d -> d
getNoHtmlDoc = runIdentity . unNoHtmlDoc

instance NFData d => NFData (NoHtmlDoc d) where
    rnf = rnf . getNoHtmlDoc

instance Monoid d => Monoid (NoHtmlDoc d) where
  mempty = pure mempty
  mappend = liftA2 mappend

instance Document d => Document (NoHtmlDoc d) where
  char = pure . char
  text = pure . text
  zeroWidthText = pure . zeroWidthText
  (<->) = liftA2 (<->)
  hcat  = liftA hcat . sequenceA
  hsep  = liftA hsep . sequenceA
  ($$)  = liftA2 ($$)
  ($-$) = liftA2 ($-$)
  vcat  = liftA vcat  . sequenceA
  sep   = liftA sep   . sequenceA
  cat   = liftA cat   . sequenceA
  fsep  = liftA fsep  . sequenceA
  fcat  = liftA fcat  . sequenceA
  nest  = liftA2 nest . pure
  caseEmptyDoc = liftA3 caseEmptyDoc

instance Document d => HtmlDocument (NoHtmlDoc d) where
    unescapedText          = noHtmlDoc . text
    unescapedZeroWidthText = noHtmlDoc . zeroWidthText

instance Document d => HighlightDocument (NoHtmlDoc d) where
    highlight _ = id
