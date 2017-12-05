module Shape_abs

export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

public export
data ShapeView : Shape -> Type where
  STriangle : ShapeView (triangle x y)
  SRectangle : ShapeView (rectangle x y)
  SCircle : ShapeView (circle z)

export
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle
