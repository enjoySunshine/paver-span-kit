/**
 * @author       Richard Davey <rich@phaser.io>
 * @copyright    2013-2026 Phaser Studio Inc.
 * @license      {@link https://opensource.org/licenses/MIT|MIT License}
 */

var Geom = require('../../geom/');
var Intersects = require('../../geom/intersects/');
var GetFastValue = require('../../utils/object/GetFastValue');
var NOOP = require('../../utils/NOOP');
var Vector2 = require('../../math/Vector2');
var CONST = require('../const/ORIENTATION_CONST');

var point = new Vector2();
var pointStart = new Vector2();
var pointEnd = new Vector2();

//  Scratch arrays for the per-column and per-row world positions, reused between calls.
var colScratch = new Float64Array(0);
var rowScratch = new Float64Array(0);

//  Scratch holders for the horizontal extent of a shape within a horizontal band.
var bandMin = 0;
var bandMax = 0;

//  Shape ids for the fast paths.
var SHAPE_NONE = 0;
var SHAPE_CIRCLE = 1;
var SHAPE_RECTANGLE = 2;
var SHAPE_TRIANGLE = 3;
var SHAPE_LINE = 4;

/**
 * Inline equivalent of `Phaser.Geom.Intersects.LineToLine`, using plain numbers. This performs
 * exactly the same checks and arithmetic, in the same order, as the Line version, but without
 * creating or reading any objects.
 *
 * @ignore
 */
var lineToLine = function (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2)
{
    if ((ax1 === ax2 && ay1 === ay2) || (bx1 === bx2 && by1 === by2))
    {
        return false;
    }

    var denom = ((by2 - by1) * (ax2 - ax1) - (bx2 - bx1) * (ay2 - ay1));

    if (denom === 0)
    {
        return false;
    }

    var ua = ((bx2 - bx1) * (ay1 - by1) - (by2 - by1) * (ax1 - bx1)) / denom;
    var ub = ((ax2 - ax1) * (ay1 - by1) - (ay2 - ay1) * (ax1 - bx1)) / denom;

    return !(ua < 0 || ua > 1 || ub < 0 || ub > 1);
};

/**
 * Inline equivalent of `Phaser.Geom.Intersects.LineToRectangle`, using plain numbers.
 * Performs exactly the same checks and arithmetic as the shape-based version.
 *
 * @ignore
 */
var lineToRectangle = function (lx1, ly1, lx2, ly2, rx, ry, rw, rh)
{
    var bx1 = rx;
    var by1 = ry;
    var bx2 = rx + rw;
    var by2 = ry + rh;

    var t;

    if ((lx1 >= bx1 && lx1 <= bx2 && ly1 >= by1 && ly1 <= by2) ||
        (lx2 >= bx1 && lx2 <= bx2 && ly2 >= by1 && ly2 <= by2))
    {
        return true;
    }

    if (lx1 < bx1 && lx2 >= bx1)
    {
        t = ly1 + (ly2 - ly1) * (bx1 - lx1) / (lx2 - lx1);

        if (t > by1 && t <= by2)
        {
            return true;
        }
    }
    else if (lx1 > bx2 && lx2 <= bx2)
    {
        t = ly1 + (ly2 - ly1) * (bx2 - lx1) / (lx2 - lx1);

        if (t >= by1 && t <= by2)
        {
            return true;
        }
    }

    if (ly1 < by1 && ly2 >= by1)
    {
        t = lx1 + (lx2 - lx1) * (by1 - ly1) / (ly2 - ly1);

        if (t >= bx1 && t <= bx2)
        {
            return true;
        }
    }
    else if (ly1 > by2 && ly2 <= by2)
    {
        t = lx1 + (lx2 - lx1) * (by2 - ly1) / (ly2 - ly1);

        if (t >= bx1 && t <= bx2)
        {
            return true;
        }
    }

    return false;
};

/**
 * Inline equivalent of the barycentric point test used by `Phaser.Geom.Triangle.ContainsArray`.
 *
 * @ignore
 */
var pointInTriangle = function (px, py, x1, y1, v0x, v0y, v1x, v1y, dot00, dot01, dot11, inv)
{
    var v2x = px - x1;
    var v2y = py - y1;

    var dot02 = (v0x * v2x) + (v0y * v2y);
    var dot12 = (v1x * v2x) + (v1y * v2y);

    var u = ((dot11 * dot02) - (dot01 * dot12)) * inv;
    var v = ((dot00 * dot12) - (dot01 * dot02)) * inv;

    return (u >= 0 && v >= 0 && (u + v < 1));
};

/**
 * Inline equivalent of `Phaser.Geom.Intersects.RectangleToTriangle`, using plain numbers and
 * triangle data that has been pre-computed once per query. Returns the same result as the
 * shape-based version, without allocating Line objects or corner point arrays for each tile.
 *
 * @ignore
 */
var rectToTriangle = function (
    rx, ry, rw, rh,
    x1, y1, x2, y2, x3, y3,
    tLeft, tRight, tTop, tBottom,
    v0x, v0y, v1x, v1y, dot00, dot01, dot11, inv, hasInv)
{
    var rRight = rx + rw;
    var rBottom = ry + rh;

    if (tLeft > rRight || tRight < rx || tTop > rBottom || tBottom < ry)
    {
        return false;
    }

    //  Rectangle.Contains, which is always false for an empty rectangle.
    if (rw > 0 && rh > 0)
    {
        if ((rx <= x1 && rRight >= x1 && ry <= y1 && rBottom >= y1) ||
            (rx <= x2 && rRight >= x2 && ry <= y2 && rBottom >= y2) ||
            (rx <= x3 && rRight >= x3 && ry <= y3 && rBottom >= y3))
        {
            return true;
        }
    }

    //  Triangle edge A against the top, right, bottom and left edges of the rectangle.
    if (lineToLine(x1, y1, x2, y2, rx, ry, rRight, ry) ||
        lineToLine(x1, y1, x2, y2, rRight, ry, rRight, rBottom) ||
        lineToLine(x1, y1, x2, y2, rRight, rBottom, rx, rBottom) ||
        lineToLine(x1, y1, x2, y2, rx, rBottom, rx, ry))
    {
        return true;
    }

    //  Triangle edge B.
    if (lineToLine(x2, y2, x3, y3, rx, ry, rRight, ry) ||
        lineToLine(x2, y2, x3, y3, rRight, ry, rRight, rBottom) ||
        lineToLine(x2, y2, x3, y3, rRight, rBottom, rx, rBottom) ||
        lineToLine(x2, y2, x3, y3, rx, rBottom, rx, ry))
    {
        return true;
    }

    //  Triangle edge C.
    if (lineToLine(x3, y3, x1, y1, rx, ry, rRight, ry) ||
        lineToLine(x3, y3, x1, y1, rRight, ry, rRight, rBottom) ||
        lineToLine(x3, y3, x1, y1, rRight, rBottom, rx, rBottom) ||
        lineToLine(x3, y3, x1, y1, rx, rBottom, rx, ry))
    {
        return true;
    }

    //  No edges cross, so check the rectangle corners against the triangle.
    if (hasInv)
    {
        return (
            pointInTriangle(rx, ry, x1, y1, v0x, v0y, v1x, v1y, dot00, dot01, dot11, inv) ||
            pointInTriangle(rRight, ry, x1, y1, v0x, v0y, v1x, v1y, dot00, dot01, dot11, inv) ||
            pointInTriangle(rRight, rBottom, x1, y1, v0x, v0y, v1x, v1y, dot00, dot01, dot11, inv) ||
            pointInTriangle(rx, rBottom, x1, y1, v0x, v0y, v1x, v1y, dot00, dot01, dot11, inv)
        );
    }

    return false;
};

/**
 * Narrows the horizontal extent of a triangle within a horizontal band, storing the result in
 * `bandMin` and `bandMax`. Whole rows of tiles that cannot possibly touch the triangle are
 * skipped by the caller.
 *
 * The range is padded by `pad` on both sides, so it can only ever be too wide - never too
 * narrow - and the exact per-tile test remains the only thing that can accept a tile.
 *
 * @ignore
 */
var triangleBand = function (bandTop, bandBottom, pad, x1, y1, x2, y2, x3, y3)
{
    var minX = Infinity;
    var maxX = -Infinity;
    var x;

    if (y1 >= bandTop && y1 <= bandBottom) { if (x1 < minX) { minX = x1; } if (x1 > maxX) { maxX = x1; } }
    if (y2 >= bandTop && y2 <= bandBottom) { if (x2 < minX) { minX = x2; } if (x2 > maxX) { maxX = x2; } }
    if (y3 >= bandTop && y3 <= bandBottom) { if (x3 < minX) { minX = x3; } if (x3 > maxX) { maxX = x3; } }

    //  Edge 1-2
    if (y1 !== y2)
    {
        if ((bandTop >= y1) !== (bandTop >= y2))
        {
            x = x1 + (x2 - x1) * (bandTop - y1) / (y2 - y1);
            if (x < minX) { minX = x; }
            if (x > maxX) { maxX = x; }
        }

        if ((bandBottom > y1) !== (bandBottom > y2))
        {
            x = x1 + (x2 - x1) * (bandBottom - y1) / (y2 - y1);
            if (x < minX) { minX = x; }
            if (x > maxX) { maxX = x; }
        }
    }

    //  Edge 2-3
    if (y2 !== y3)
    {
        if ((bandTop >= y2) !== (bandTop >= y3))
        {
            x = x2 + (x3 - x2) * (bandTop - y2) / (y3 - y2);
            if (x < minX) { minX = x; }
            if (x > maxX) { maxX = x; }
        }

        if ((bandBottom > y2) !== (bandBottom > y3))
        {
            x = x2 + (x3 - x2) * (bandBottom - y2) / (y3 - y2);
            if (x < minX) { minX = x; }
            if (x > maxX) { maxX = x; }
        }
    }

    //  Edge 3-1
    if (y3 !== y1)
    {
        if ((bandTop >= y3) !== (bandTop >= y1))
        {
            x = x3 + (x1 - x3) * (bandTop - y3) / (y1 - y3);
            if (x < minX) { minX = x; }
            if (x > maxX) { maxX = x; }
        }

        if ((bandBottom > y3) !== (bandBottom > y1))
        {
            x = x3 + (x1 - x3) * (bandBottom - y3) / (y1 - y3);
            if (x < minX) { minX = x; }
            if (x > maxX) { maxX = x; }
        }
    }

    if (minX === Infinity)
    {
        return false;
    }

    bandMin = minX - pad;
    bandMax = maxX + pad;

    return true;
};

/**
 * Narrows the horizontal extent of a line segment within a horizontal band, storing the result
 * in `bandMin` and `bandMax`. The range is padded by `pad` on both sides, so it can only ever
 * be too wide.
 *
 * @ignore
 */
var lineBand = function (bandTop, bandBottom, pad, x1, y1, x2, y2)
{
    var dx = x2 - x1;
    var dy = y2 - y1;
    var xa;
    var xb;

    if (dy === 0)
    {
        if (y1 < bandTop || y1 > bandBottom)
        {
            return false;
        }

        xa = x1;
        xb = x2;
    }
    else
    {
        var ta = (bandTop - y1) / dy;
        var tb = (bandBottom - y1) / dy;

        var tMin = Math.max(0, Math.min(ta, tb));
        var tMax = Math.min(1, Math.max(ta, tb));

        if (tMin > tMax)
        {
            return false;
        }

        xa = x1 + tMin * dx;
        xb = x1 + tMax * dx;
    }

    bandMin = Math.min(xa, xb) - pad;
    bandMax = Math.max(xa, xb) + pad;

    return true;
};

/**
 * Gets the tiles that overlap with the given shape in the given layer. The shape must be a Circle,
 * Line, Rectangle or Triangle. The shape should be in world coordinates.
 *
 * **Note:** This method currently only works with orthogonal tilemap layers.
 *
 * @function Phaser.Tilemaps.Components.GetTilesWithinShape
 * @since 3.0.0
 *
 * @param {(Phaser.Geom.Circle|Phaser.Geom.Line|Phaser.Geom.Rectangle|Phaser.Geom.Triangle)} shape - A shape in world (pixel) coordinates
 * @param {Phaser.Types.Tilemaps.FilteringOptions} filteringOptions - Optional filters to apply when getting the tiles.
 * @param {Phaser.Cameras.Scene2D.Camera} camera - The Camera to use when calculating the tile index from the world values.
 * @param {Phaser.Tilemaps.LayerData} layer - The Tilemap Layer to act upon.
 *
 * @return {Phaser.Tilemaps.Tile[]} An array of Tile objects that intersect with the given shape, or an empty array if no tiles overlap or the layer is not orthogonal.
 */
var GetTilesWithinShape = function (shape, filteringOptions, camera, layer)
{
    if (layer.orientation !== CONST.ORTHOGONAL)
    {
        console.warn('GetTilesWithinShape only works with orthogonal tilemaps');
        return [];
    }

    if (shape === undefined) { return []; }

    // intersectTest is a function with parameters: shape, rect
    var intersectTest = NOOP;
    var shapeType = SHAPE_NONE;

    if (shape instanceof Geom.Circle)
    {
        intersectTest = Intersects.CircleToRectangle;
        shapeType = SHAPE_CIRCLE;
    }
    else if (shape instanceof Geom.Rectangle)
    {
        intersectTest = Intersects.RectangleToRectangle;
        shapeType = SHAPE_RECTANGLE;
    }
    else if (shape instanceof Geom.Triangle)
    {
        intersectTest = Intersects.RectangleToTriangle;
        shapeType = SHAPE_TRIANGLE;
    }
    else if (shape instanceof Geom.Line)
    {
        intersectTest = Intersects.LineToRectangle;
        shapeType = SHAPE_LINE;
    }

    // Top left corner of the shapes's bounding box, rounded down to include partial tiles
    layer.tilemapLayer.worldToTileXY(shape.left, shape.top, true, pointStart, camera);

    var xStart = pointStart.x;
    var yStart = pointStart.y;

    // Bottom right corner of the shapes's bounding box, rounded up to include partial tiles
    layer.tilemapLayer.worldToTileXY(shape.right, shape.bottom, false, pointEnd, camera);

    var xEnd = Math.ceil(pointEnd.x);
    var yEnd = Math.ceil(pointEnd.y);

    // Tiles within bounding rectangle of shape. Bounds are forced to be at least 1 x 1 tile in size
    // to grab tiles for shapes that don't have a height or width (e.g. a horizontal line).
    var width = Math.max(xEnd - xStart, 1);
    var height = Math.max(yEnd - yStart, 1);

    //  This is the same clipping that GetTilesWithin applies, done up front so that no work is
    //  done for tiles outside of the layer.
    if (xStart < 0)
    {
        width += xStart;
        xStart = 0;
    }

    if (yStart < 0)
    {
        height += yStart;
        yStart = 0;
    }

    if (xStart + width > layer.width)
    {
        width = Math.max(layer.width - xStart, 0);
    }

    if (yStart + height > layer.height)
    {
        height = Math.max(layer.height - yStart, 0);
    }

    if (!filteringOptions) { filteringOptions = {}; }

    var isNotEmpty = GetFastValue(filteringOptions, 'isNotEmpty', false);
    var isColliding = GetFastValue(filteringOptions, 'isColliding', false);
    var hasInterestingFace = GetFastValue(filteringOptions, 'hasInterestingFace', false);

    var tilemapLayer = layer.tilemapLayer;
    var data = layer.data;
    var results = [];

    var tileWidth = layer.tileWidth;
    var tileHeight = layer.tileHeight;

    if (tilemapLayer)
    {
        tileWidth *= tilemapLayer.scaleX;
        tileHeight *= tilemapLayer.scaleY;
    }

    var row;
    var tile;
    var tx;
    var ty;

    if (width <= 0 || height <= 0)
    {
        return results;
    }

    if (shapeType === SHAPE_LINE || shapeType === SHAPE_TRIANGLE)
    {
        //  World positions are linear in tile index for orthogonal layers, so the X position of
        //  each column and the Y position of each row only need resolving once. This avoids
        //  calling tileToWorldXY for every tile in a large bounding box.
        if (colScratch.length < width) { colScratch = new Float64Array(width); }
        if (rowScratch.length < height) { rowScratch = new Float64Array(height); }

        var colX = colScratch;
        var rowY = rowScratch;

        for (tx = 0; tx < width; tx++)
        {
            tilemapLayer.tileToWorldXY(xStart + tx, 0, point, camera);
            colX[tx] = point.x;
        }

        for (ty = 0; ty < height; ty++)
        {
            tilemapLayer.tileToWorldXY(0, yStart + ty, point, camera);
            rowY[ty] = point.y;
        }

        //  Used to map a world X range onto a range of column indices. This is only safe if
        //  columns are laid out left to right at a constant step, so that is checked here.
        var colStep = (width > 1) ? (colX[1] - colX[0]) : tileWidth;
        var useColRange = (colStep > 0);
        var colFirst;
        var colLast;

        if (useColRange && width > 2)
        {
            var expectedLast = colX[0] + colStep * (width - 1);
            var tolerance = (Math.abs(colX[0]) + Math.abs(expectedLast) + Math.abs(colStep) * width + 1) * 1e-9;

            if (Math.abs(colX[width - 1] - expectedLast) > tolerance)
            {
                useColRange = false;
            }
        }

        var pad = Math.abs(tileWidth) + Math.abs(colStep);
        var bandTop;
        var bandBottom;

        if (shapeType === SHAPE_LINE)
        {
            var lx1 = shape.x1;
            var ly1 = shape.y1;
            var lx2 = shape.x2;
            var ly2 = shape.y2;

            for (ty = 0; ty < height; ty++)
            {
                var ry = rowY[ty];

                bandTop = ry;
                bandBottom = ry + tileHeight;

                if (bandTop > bandBottom)
                {
                    bandTop = bandBottom;
                    bandBottom = ry;
                }

                if (!lineBand(bandTop, bandBottom, pad, lx1, ly1, lx2, ly2))
                {
                    continue;
                }

                if (useColRange)
                {
                    colFirst = Math.floor((bandMin - colX[0]) / colStep) - 1;
                    colLast = Math.ceil((bandMax - colX[0]) / colStep) + 1;

                    if (colFirst < 0) { colFirst = 0; }
                    if (colLast > width - 1) { colLast = width - 1; }
                    if (colFirst > colLast) { continue; }
                }
                else
                {
                    colFirst = 0;
                    colLast = width - 1;
                }

                row = data[yStart + ty];

                if (!row) { continue; }

                for (tx = colFirst; tx <= colLast; tx++)
                {
                    tile = row[xStart + tx];

                    if (tile === null) { continue; }

                    if (isNotEmpty && tile.index === -1) { continue; }
                    if (isColliding && !tile.collides) { continue; }
                    if (hasInterestingFace && !tile.hasInterestingFace) { continue; }

                    if (lineToRectangle(lx1, ly1, lx2, ly2, colX[tx], ry, tileWidth, tileHeight))
                    {
                        results.push(tile);
                    }
                }
            }
        }
        else
        {
            var x1 = shape.x1;
            var y1 = shape.y1;
            var x2 = shape.x2;
            var y2 = shape.y2;
            var x3 = shape.x3;
            var y3 = shape.y3;

            var tLeft = Math.min(x1, x2, x3);
            var tRight = Math.max(x1, x2, x3);
            var tTop = Math.min(y1, y2, y3);
            var tBottom = Math.max(y1, y2, y3);

            //  Barycentric data for the corner-in-triangle checks, matching Triangle.ContainsArray.
            var v0x = x3 - x1;
            var v0y = y3 - y1;
            var v1x = x2 - x1;
            var v1y = y2 - y1;
            var dot00 = (v0x * v0x) + (v0y * v0y);
            var dot01 = (v0x * v1x) + (v0y * v1y);
            var dot11 = (v1x * v1x) + (v1y * v1y);
            var b = ((dot00 * dot11) - (dot01 * dot01));
            var inv = (b === 0) ? 0 : (1 / b);
            var hasInv = (b !== 0);

            for (ty = 0; ty < height; ty++)
            {
                var triY = rowY[ty];

                bandTop = triY;
                bandBottom = triY + tileHeight;

                if (bandTop > bandBottom)
                {
                    bandTop = bandBottom;
                    bandBottom = triY;
                }

                if (!triangleBand(bandTop, bandBottom, pad, x1, y1, x2, y2, x3, y3))
                {
                    continue;
                }

                if (useColRange)
                {
                    colFirst = Math.floor((bandMin - colX[0]) / colStep) - 1;
                    colLast = Math.ceil((bandMax - colX[0]) / colStep) + 1;

                    if (colFirst < 0) { colFirst = 0; }
                    if (colLast > width - 1) { colLast = width - 1; }
                    if (colFirst > colLast) { continue; }
                }
                else
                {
                    colFirst = 0;
                    colLast = width - 1;
                }

                row = data[yStart + ty];

                if (!row) { continue; }

                for (tx = colFirst; tx <= colLast; tx++)
                {
                    tile = row[xStart + tx];

                    if (tile === null) { continue; }

                    if (isNotEmpty && tile.index === -1) { continue; }
                    if (isColliding && !tile.collides) { continue; }
                    if (hasInterestingFace && !tile.hasInterestingFace) { continue; }

                    if (rectToTriangle(
                        colX[tx], triY, tileWidth, tileHeight,
                        x1, y1, x2, y2, x3, y3,
                        tLeft, tRight, tTop, tBottom,
                        v0x, v0y, v1x, v1y, dot00, dot01, dot11, inv, hasInv))
                    {
                        results.push(tile);
                    }
                }
            }
        }
    }
    else
    {
        //  Circle and Rectangle shapes keep using the shape intersection functions. Their
        //  bounding boxes are typically small, so resolving each tile rect is cheap.
        var tileRect = new Geom.Rectangle(0, 0, tileWidth, tileHeight);

        for (ty = 0; ty < height; ty++)
        {
            row = data[yStart + ty];

            if (!row) { continue; }

            for (tx = 0; tx < width; tx++)
            {
                tile = row[xStart + tx];

                if (tile === null) { continue; }

                if (isNotEmpty && tile.index === -1) { continue; }
                if (isColliding && !tile.collides) { continue; }
                if (hasInterestingFace && !tile.hasInterestingFace) { continue; }

                tilemapLayer.tileToWorldXY(tile.x, tile.y, point, camera);

                tileRect.x = point.x;
                tileRect.y = point.y;

                if (intersectTest(shape, tileRect))
                {
                    results.push(tile);
                }
            }
        }
    }

    return results;
};

module.exports = GetTilesWithinShape;
