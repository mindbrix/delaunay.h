// Source: http://paulbourke.net/papers/triangulate/triangulate.c
//
#include <stdlib.h>
#include <math.h>

#pragma clang diagnostic ignored "-Wcomma"

typedef struct {
    int p1, p2, p3;
} ITRIANGLE;
typedef struct {
    int p1, p2;
} IEDGE;
typedef struct {
    float x, y;
    int i;
} XYZ;
typedef struct {
    double xmax;
} CIRCLE;


static double incircle(double xp, double yp, double x1, double y1, double x2, double y2, double x3, double y3) {
    double adx, ady, bdx, bdy, cdx, cdy;
    double abdet, bcdet, cadet;
    double alift, blift, clift;
    
    adx = x1 - xp, ady = y1 - yp;
    bdx = x2 - xp, bdy = y2 - yp;
    cdx = x3 - xp, cdy = y3 - yp;
    
    abdet = adx * bdy - bdx * ady;
    bcdet = bdx * cdy - cdx * bdy;
    cadet = cdx * ady - adx * cdy;
    
    alift = adx * adx + ady * ady;
    blift = bdx * bdx + bdy * bdy;
    clift = cdx * cdx + cdy * cdy;
    
    return alift * bcdet + blift * cadet + clift * abdet;
}

static void circumcenter(double ax, double ay, double bx, double by, double cx, double cy, double *xc, double *yc, double *xmax) {
    double dx, dy, ex, ey;
    double bl, cl, d, r;
    
    dx = bx - ax, dy = by - ay;
    bl = dx * dx + dy * dy;
    
    ex = cx - ax, ey = cy - ay;
    cl = ex * ex + ey * ey;
    
    d = dx * ey - dy * ex;
    
    *xc = (ey * bl - dy * cl) * 0.5 / d;
    *yc = (dx * cl - ex * bl) * 0.5 / d;
    
    r = sqrt(*xc * *xc + *yc * *yc);
    
    *xc += ax, *yc += ay;
    *xmax = *xc + r;
}

static int XYZCompare(const void *v1, const void *v2) {
    XYZ *p1 = (XYZ *)v1;
    XYZ *p2 = (XYZ *)v2;
    if (p1->x < p2->x)
        return(-1);
    else if (p1->x > p2->x)
        return(1);
    else
        return(0);
}

/*
 Triangulation subroutine
 Takes as input NV vertices in array pxyz
 Returned is a list of ntri triangular faces in the array v
 These triangles are arranged in a consistent CCW order.
 The triangle array 'v' should be malloced to 4 * nv
 The vertex array pxyz must be big enough to hold 3 more points
 */
static int Triangulate(int nv, XYZ *pxyz, ITRIANGLE *v, int vsize, int *ntri)
{
    ITRIANGLE *completed = v, *vend = v + vsize, *vstart = vend, *tri;
    CIRCLE *circles = NULL, *circle;
    IEDGE *edges = NULL;
    int nedge = 0, emax = 200, status = 0;
    int i, j, k;
    double xp, yp, x1, y1, x2, y2, x3, y3, xc, yc, xmaxc;
    double xmin, xmax, ymin, ymax, xmid, ymid;
    double dx, dy, dmax;
    
    qsort((void *)pxyz, (size_t)nv, sizeof(XYZ), XYZCompare);
    
    if ((circles = (CIRCLE *)malloc(vsize*sizeof(CIRCLE))) == NULL) {
        status = 5;
        goto skip;
    }
    
    if ((edges = (IEDGE *)malloc(emax*(long)sizeof(IEDGE))) == NULL) {
        status = 2;
        goto skip;
    }
    
    // AABB
    //
    xmin = pxyz[0].x, ymin = pxyz[0].y;
    xmax = xmin, ymax = ymin;
    
    for (i = 1; i < nv; i++) {
        if (pxyz[i].x < xmin) xmin = pxyz[i].x;
        if (pxyz[i].x > xmax) xmax = pxyz[i].x;
        if (pxyz[i].y < ymin) ymin = pxyz[i].y;
        if (pxyz[i].y > ymax) ymax = pxyz[i].y;
    }
    dx = xmax - xmin;
    dy = ymax - ymin;
    dmax = (dx > dy) ? dx : dy;
    xmid = (xmax + xmin) * 0.5;
    ymid = (ymax + ymin) * 0.5;
    
    // CCW Super triangle
    //
    pxyz[nv + 2].x = x1 = xmid - 20 * dmax;
    pxyz[nv + 2].y = y1 = ymid - dmax;
    pxyz[nv + 1].x = x2 = xmid;
    pxyz[nv + 1].y = y2 = ymid + 20 * dmax;
    pxyz[nv + 0].x = x3 = xmid + 20 * dmax;
    pxyz[nv + 0].y = y3 = ymid - dmax;
    
    vstart--;
    vstart->p1 = nv, vstart->p2 = nv + 1, vstart->p3 = nv + 2;
    circumcenter(x1, y1, x2, y2, x3, y3, &xc, &yc, &xmaxc);
    circles[vsize - 1].xmax = xmaxc;
    
    xp = yp = FLT_MAX;
    
    for (i = 0; i < nv; i++) {
        
        if (xp == pxyz[i].x && yp == pxyz[i].y)
            continue;
        
        xp = pxyz[i].x;
        yp = pxyz[i].y;
        nedge = 0;
        
        // Filter out completed triangles
        //
        for (tri = vstart; tri < vend; tri++) {
            circle = & circles[tri - v];

            if (xp > circle->xmax) {
                if (tri->p1 < nv && tri->p2 < nv && tri->p3 < nv)
                     *completed++ = *tri;
                
                circles[tri - v] = circles[vstart - v];
                *tri = *vstart++;
            }
        }
        
        // Create new polygon edge list from incircle triangles
        //
        for (tri = vstart; tri < vend; tri++) {
            x1 = pxyz[tri->p1].x, y1 = pxyz[tri->p1].y;
            x2 = pxyz[tri->p2].x, y2 = pxyz[tri->p2].y;
            x3 = pxyz[tri->p3].x, y3 = pxyz[tri->p3].y;
            
            if (incircle(xp, yp, x1, y1, x2, y2, x3, y3) >= 0) {
                if (nedge + 3 >= emax) {
                    emax += 100;
                    if ((edges = (IEDGE *)realloc(edges, emax * (long)sizeof(IEDGE))) == NULL) {
                        status = 3;
                        goto skip;
                    }
                }
                edges[nedge + 0].p1 = tri->p1, edges[nedge + 0].p2 = tri->p2;
                edges[nedge + 1].p1 = tri->p2, edges[nedge + 1].p2 = tri->p3;
                edges[nedge + 2].p1 = tri->p3, edges[nedge + 2].p2 = tri->p1;
                nedge += 3;
                
                circles[tri - v] = circles[vstart - v];
                *tri = *vstart++;
            }
        }
        
        // Filter out matching half edges to create a polygon
        //
        for (j = 0; j < nedge - 1; j++) {
            for (k = j + 1; k < nedge; k++) {
                if ((edges[j].p1 == edges[k].p2 && edges[j].p2 == edges[k].p1) ||
                    (edges[j].p1 == edges[k].p1 && edges[j].p2 == edges[k].p2)) {
                    edges[j].p1 = -1, edges[j].p2 = -1;
                    edges[k].p1 = -1, edges[k].p2 = -1;
                }
            }
        }
        
        // Create a Delaunay triangle fan from the polygon
        //
        for (j = 0; j <nedge; j++) {
            if (edges[j].p1 < 0 || edges[j].p2 < 0)
                continue;
            
            if (vstart == completed) {
                status = 4;
                goto skip;
            }
            
            --vstart;
            vstart->p1 = edges[j].p1;
            vstart->p2 = edges[j].p2;
            vstart->p3 = i;
            
            x1 = pxyz[vstart->p1].x, y1 = pxyz[vstart->p1].y;
            x2 = pxyz[vstart->p2].x, y2 = pxyz[vstart->p2].y;
            x3 = pxyz[vstart->p3].x, y3 = pxyz[vstart->p3].y;
            
            circumcenter(x1, y1, x2, y2, x3, y3, &xc, &yc, &xmaxc);
            circles[vstart - v].xmax = xmaxc;
        }
    }
    
    // Copy over remaining completed triangles not touching the super triangle
    //
    for (tri = vstart; tri < vend; tri++)
        if (tri->p1 < nv && tri->p2 < nv && tri->p3 < nv)
            *completed++ = *tri;
    
    (*ntri) = (int)(completed - v);
    
skip:
    free(circles);
    free(edges);
    return(status);
}

