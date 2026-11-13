module ObsEval where
import Common
import Metacontext
import Syntax
import Value
import Cxt.Type
import Definition

reduceOeq :: HasGlobal => Spine -> Maybe Val
reduceCast :: HasGlobal => Spine -> Maybe Val