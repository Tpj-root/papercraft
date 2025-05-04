/** \file
 * Unfold an STL file into a set of laser-cutable polygons.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <unistd.h>
#include <math.h>
#include <err.h>
#include <assert.h>
#include "v3.h"

#ifndef M_PI
#define M_PI   3.1415926535897932384
#endif

#define EPS 1e-6

static int debug = 0;
static int draw_labels = 0;

typedef struct
{
    char header[80];
    uint32_t num_triangles;
} __attribute__((__packed__))
stl_header_t;

typedef struct
{
    v3_t normal;
    v3_t p[3];
    uint16_t attr;
} __attribute__((__packed__))
stl_face_t;

typedef struct face face_t;
typedef struct poly poly_t;

struct face
{
    float sides[3];
    face_t * next[3];
    int next_edge[3];
    int coplanar[3];
    int used;
};

struct poly
{
    int start_edge;
    int printed;

    float a;
    float x2;
    float y2;
    float rot;

    float p[3][2];

    face_t * face;
    poly_t * next[3];
    poly_t * work_next;
};

static int
edge_eq2(
    const stl_face_t * const t0,
    const stl_face_t * const t1,
    int e0,
    int e1
)
{
    const v3_t * const v00 = &t0->p[e0];
    const v3_t * const v01 = &t0->p[(e0+1) % 3];
    const v3_t * const v10 = &t1->p[e1];
    const v3_t * const v11 = &t1->p[(e1+1) % 3];

    if (v3_eq(*v00, *v11) && v3_eq(*v01, *v10))
        return 1;

    return 0;
}

void
svg_line(
    const char * color,
    const float * p1,
    const float * p2,
    int dash
)
{
    if (!dash)
    {
        printf("<line x1=\"%f\" y1=\"%f\" x2=\"%f\" y2=\"%f\" stroke=\"%s\" stroke-width=\"0.1px\"/>\n",
            p1[0], p1[1], p2[0], p2[1], color);
        return;
    }

    const float dx = p2[0] - p1[0];
    const float dy = p2[1] - p1[1];

    const float h1[] = { p1[0] + dx*0.45, p1[1] + dy*0.45 };
    const float h2[] = { p1[0] + dx*0.55, p1[1] + dy*0.55 };

    svg_line(color, p1, h1, 0);
    svg_line(color, h2, p2, 0);
}

void
rotate(
    float * p,
    const float * origin,
    float a,
    float x,
    float y
)
{
    p[0] = cos(a) * x - sin(a) * y + origin[0];
    p[1] = sin(a) * x + cos(a) * y + origin[1];
}

void
poly_position(
    poly_t * const g,
    const poly_t * const g_src,
    float rot,
    float trans_x,
    float trans_y
)
{
    const face_t * const f = g->face;
    const int start_edge = g->start_edge;

    float a = f->sides[(start_edge + 0) % 3];
    float c = f->sides[(start_edge + 1) % 3];
    float b = f->sides[(start_edge + 2) % 3];
    
    // Validate triangle edges
    if (a <= EPS || b <= EPS || c <= EPS) {
        errx(EXIT_FAILURE, "Degenerate triangle edge detected");
    }
    if (a + b <= c + EPS || a + c <= b + EPS || b + c <= a + EPS) {
        errx(EXIT_FAILURE, "Invalid triangle edges: %f, %f, %f", a, b, c);
    }

    float x2 = (a*a + b*b - c*c) / (2*a);
    float discriminant = b*b - x2*x2;
    
    if (discriminant < -EPS) {
        errx(EXIT_FAILURE, "Invalid triangle configuration");
    } else if (discriminant < 0) {
        discriminant = 0;
    }
    
    float y2 = sqrt(discriminant);

    float origin[2];
    rotate(origin, g_src->p[0], g_src->rot, trans_x, trans_y);

    g->rot = g_src->rot + rot;
    g->a = a;
    g->x2 = x2;
    g->y2 = y2;

    rotate(g->p[0], origin, g->rot, 0, 0);
    rotate(g->p[1], origin, g->rot, a, 0);
    rotate(g->p[2], origin, g->rot, x2, y2);
}

static void
enqueue(
    poly_t * g,
    poly_t * const new_g,
    int at_head
)
{
    if (at_head)
    {
        new_g->work_next = g->work_next;
        g->work_next = new_g;
        return;
    }

    while (g->work_next)
        g = g->work_next;
    g->work_next = new_g;
}

static poly_t * poly_root;
static float poly_min[2], poly_max[2];

static inline int
v2_eq(
    const float p0[],
    const float p1[]
)
{
    const float dx = p0[0] - p1[0];
    const float dy = p0[1] - p1[1];
    return (-EPS < dx && dx < EPS && -EPS < dy && dy < EPS);
}

int
get_line_intersection(
    float p0_x, float p0_y,
    float p1_x, float p1_y, 
    float p2_x, float p2_y,
    float p3_x, float p3_y,
    float *i_x, float *i_y
)
{
    float s1_x = p1_x - p0_x;
    float s1_y = p1_y - p0_y;
    float s2_x = p3_x - p2_x;
    float s2_y = p3_y - p2_y;

    float denom = (-s2_x * s1_y + s1_x * s2_y);
    if (fabs(denom) < EPS)
        return 0;

    float s = (-s1_y * (p0_x - p2_x) + s1_x * (p0_y - p2_y)) / denom;
    float t = ( s2_x * (p0_y - p2_y) - s2_y * (p0_x - p2_x)) / denom;

    if (s > EPS && s < 1-EPS && t > EPS && t < 1-EPS)
    {
        if (i_x) *i_x = p0_x + (t * s1_x);
        if (i_y) *i_y = p0_y + (t * s1_y);
        return 1;
    }

    return 0;
}

int
intersect(
    const float p00[],
    const float p01[],
    const float p10[],
    const float p11[]
)
{
    if (v2_eq(p00, p10) && v2_eq(p01, p11))
        return 0;
    if (v2_eq(p01, p10) && v2_eq(p00, p11))
        return 0;

    return get_line_intersection(
        p00[0], p00[1],
        p01[0], p01[1],
        p10[0], p10[1],
        p11[0], p11[1],
        NULL, NULL
    );
}

int
overlap_poly(
    const poly_t * const g1,
    const poly_t * const g2
)
{
    if (intersect(g1->p[0], g1->p[1], g2->p[0], g2->p[1])) return 1;
    if (intersect(g1->p[0], g1->p[1], g2->p[1], g2->p[2])) return 1;
    if (intersect(g1->p[0], g1->p[1], g2->p[2], g2->p[0])) return 1;
    if (intersect(g1->p[1], g1->p[2], g2->p[0], g2->p[1])) return 1;
    if (intersect(g1->p[1], g1->p[2], g2->p[1], g2->p[2])) return 1;
    if (intersect(g1->p[1], g1->p[2], g2->p[2], g2->p[0])) return 1;
    if (intersect(g1->p[2], g1->p[0], g2->p[0], g2->p[1])) return 1;
    if (intersect(g1->p[2], g1->p[0], g2->p[1], g2->p[2])) return 1;
    if (intersect(g1->p[2], g1->p[0], g2->p[2], g2->p[0])) return 1;

    return 0;
}

int
overlap_check(
    const poly_t * g,
    const poly_t * const new_g
)
{
    if (g == new_g)
        return 0;

    while (g)
    {
        if (overlap_poly(g, new_g))
            return 1;
        g = g->work_next;
    }

    return 0;
}

int
poly_build(
    poly_t * const g
)
{
    face_t * const f = g->face;
    const int start_edge = g->start_edge;
    f->used = 1;

    for (int i = 0 ; i < 3 ; i++)
    {
        const float px = g->p[i][0];
        const float py = g->p[i][1];

        if (px < poly_min[0]) poly_min[0] = px;
        if (px > poly_max[0]) poly_max[0] = px;
        if (py < poly_min[1]) poly_min[1] = py;
        if (py > poly_max[1]) poly_max[1] = py;
    }

    if (debug) fprintf(stderr, "%p: adding to poly\n", f);

    for (int pass = 0 ; pass < 2 ; pass++)
    {
        for (int i = 0 ; i < 3 ; i++)
        {
            const int edge = (i + start_edge) % 3;
            face_t * const f2 = f->next[edge];
            assert(f2 != NULL);
            if (f2->used)
                continue;
            if (pass == 0 && f->coplanar[edge] == 0)
                continue;

            float trans_x, trans_y, rotate;
            if (i == 0)
            {
                trans_x = g->a;
                trans_y = 0;
                rotate = M_PI;
            }
            else if (i == 1)
            {
                trans_x = g->x2;
                trans_y = g->y2;
                rotate = -atan2(g->y2, g->a - g->x2);
            }
            else if (i == 2)
            {
                trans_x = 0;
                trans_y = 0;
                rotate = atan2(g->y2, g->x2);
            }
            else
            {
                errx(EXIT_FAILURE, "edge %d invalid?\n", i);
            }

            poly_t * const g2 = calloc(1, sizeof(*g2));
            if (!g2)
                err(EXIT_FAILURE, "calloc failed");
                
            g2->face = f2;
            g2->start_edge = f->next_edge[edge];

            poly_position(g2, g, rotate, trans_x, trans_y);

            if (overlap_check(poly_root, g2))
            {
                free(g2);
                continue;
            }

            g->next[i] = g2;
            g2->next[0] = g;
            f2->used = 1;

            if (f->coplanar[edge] == 0)
                enqueue(g, g2, 1);
            else
                enqueue(g, g2, 0);
        }
    }

    return 0;
}

void
svg_text(
    float x,
    float y,
    float angle,
    const char * fmt,
    ...
)
{
    printf("<g transform=\"translate(%f %f) rotate(%f)\">", x, y, angle);
    printf("<text x=\"-2\" y=\"1.5\" style=\"font-size:1.5px;\">");

    va_list ap;
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);

    printf("</text></g>\n");
}

void
poly_print(
    poly_t * const g
)
{
    const face_t * const f = g->face;
    const int start_edge = g->start_edge;

    g->printed = 1;

    printf("<g><!-- %p %d %f %f->%p %f->%p %f->%p -->\n",
        f, g->start_edge, g->rot * 180/M_PI,
        f->sides[0], f->next[0],
        f->sides[1], f->next[1],
        f->sides[2], f->next[2]);

    int cut_lines = 0;
    const uintptr_t a1 = (0x7FFFF & (uintptr_t) f) >> 3;

    for (int i = 0 ; i < 3 ; i++)
    {
        const int edge = (start_edge + i) % 3;
        poly_t * const next = g->next[i];

        if (!next)
        {
            const float * const p1 = g->p[i];
            const float * const p2 = g->p[(i+1) % 3];
            const float cx = (p2[0] + p1[0]) / 2;
            const float cy = (p2[1] + p1[1]) / 2;
            const float dx = (p2[0] - p1[0]);
            const float dy = (p2[1] - p1[1]);
            const float angle = atan2(dy, dx) * 180 / M_PI;

            svg_line("#FF0000", p1, p2, 0);
            cut_lines++;

            if (draw_labels)
            {
                uintptr_t a2 = (0x7FFFF & (uintptr_t) f->next[edge]) >> 3;
                if (a2 > a1) a2 = a1;
                svg_text(cx, cy, angle, "%04x", a2);
            }
            continue;
        }

        if (next->printed)
            continue;

        if (f->coplanar[edge] < 0)
        {
            svg_line("#00FF00", g->p[i], g->p[(i+1) % 3], 1);
        }
        else if (f->coplanar[edge] > 0)
        {
            svg_line("#00FF00", g->p[i], g->p[(i+1) % 3], 0);
        }
    }

    printf("</g>\n");

    for (int i = 0 ; i < 3 ; i++)
    {
        poly_t * const next = g->next[i];
        if (!next || next->printed)
            continue;
        poly_print(next);
    }
}

int
coplanar_check(
    const stl_face_t * const f1,
    const stl_face_t * const f2
)
{
    v3_t x1 = f1->p[0];
    v3_t x2 = f1->p[1];
    v3_t x3 = f1->p[2];
    v3_t x4;

    for (int i = 0 ; i < 3 ; i++)
    {
        x4 = f2->p[i];
        if (v3_eq(x1, x4)) continue;
        if (v3_eq(x2, x4)) continue;
        if (v3_eq(x3, x4)) continue;
        break;
    }

    v3_t dx31 = v3_sub(x3, x1);
    v3_t dx21 = v3_sub(x2, x1);
    v3_t dx43 = v3_sub(x4, x3);
    v3_t cross = v3_cross(dx21, dx43);
    float dot = v3_dot(dx31, cross);
    
    int check = -EPS < dot && dot < +EPS;
    if (debug) fprintf(stderr, "%p %p %s: %f\n", f1, f2, check ? "yes" : "no", dot);
    return (int) dot;
}

face_t *
stl2faces(
    const stl_face_t * const stl_faces,
    const int num_triangles
)
{
    face_t * const faces = calloc(num_triangles, sizeof(*faces));
    if (!faces)
        err(EXIT_FAILURE, "calloc failed");

    for (int i = 0 ; i < num_triangles ; i++)
    {
        const stl_face_t * const stl = &stl_faces[i];
        face_t * const f = &faces[i];

        f->sides[0] = v3_len(&stl->p[0], &stl->p[1]);
        f->sides[1] = v3_len(&stl->p[1], &stl->p[2]);
        f->sides[2] = v3_len(&stl->p[2], &stl->p[0]);
        
        if (f->sides[0] < EPS || f->sides[1] < EPS || f->sides[2] < EPS) {
            errx(EXIT_FAILURE, "Degenerate triangle at index %d", i);
        }
        if (debug) fprintf(stderr, "%p %f %f %f\n",
            f, f->sides[0], f->sides[1], f->sides[2]);
    }

    for (int i = 0 ; i < num_triangles ; i++)
    {
        const stl_face_t * const stl = &stl_faces[i];
        face_t * const f = &faces[i];

        for (int j = 0 ; j < num_triangles ; j++)
        {
            if (i == j)
                continue;

            const stl_face_t * const stl2 = &stl_faces[j];
            face_t * const f2 = &faces[j];

            for (int edge = 0 ; edge < 3 ; edge++)
            {
                if (f->next[edge])
                    continue;

                for (int edge2 = 0 ; edge2 < 3 ; edge2++)
                {
                    if (f2->next[edge2])
                        continue;

                    if (!edge_eq2(stl, stl2, edge, edge2))
                        continue;

                    f->next[edge] = f2;
                    f->next_edge[edge] = edge2;
                    f2->next[edge2] = f;
                    f2->next_edge[edge2] = edge;

                    f->coplanar[edge] =
                    f2->coplanar[edge2] = coplanar_check(stl, stl2);
                }
            }
        }

        if (!(f->next[0] && f->next[1] && f->next[2]))
        {
            fprintf(stderr, "%d missing edges?\n", i);
            free(faces);
            return NULL;
        }
    }

    return faces;
}

int main(int argc, char *argv[])
{
    if (argc != 2) {
        fprintf(stderr, "Usage: %s input.stl\n", argv[0]);
        return EXIT_FAILURE;
    }

    FILE *f = fopen(argv[1], "rb");
    if (!f) {
        perror("fopen failed");
        return EXIT_FAILURE;
    }

    fseek(f, 0, SEEK_END);
    long file_size = ftell(f);
    fseek(f, 0, SEEK_SET);

    uint8_t *buf = malloc(file_size);
    if (!buf) {
        perror("malloc failed");
        fclose(f);
        return EXIT_FAILURE;
    }

    if (fread(buf, 1, file_size, f) != file_size) {
        perror("fread failed");
        fclose(f);
        free(buf);
        return EXIT_FAILURE;
    }
    fclose(f);

    const stl_header_t * const hdr = (const void*) buf;
    const stl_face_t * const stl_faces = (const void*)(hdr+1);
    const int num_triangles = hdr->num_triangles;

    fprintf(stderr, "header: '%s'\n", hdr->header);
    fprintf(stderr, "num: %d\n", num_triangles);

    face_t * const faces = stl2faces(stl_faces, num_triangles);
    if (!faces) {
        free(buf);
        return EXIT_FAILURE;
    }

    printf("<svg xmlns=\"http://www.w3.org/2000/svg\">\n");
    poly_t origin = { };

    float last_x = 0;
    float last_y = 0;

    srand48(getpid());
    int offset = lrand48();
    fprintf(stderr, "Starting at poly %d\n", offset % num_triangles);
    int group_count = 0;

    for (int i = 0 ; i < num_triangles ; i++)
    {
        face_t * const f = &faces[(i+offset) % num_triangles];
        if (f->used)
            continue;
            
        poly_t g = { .face = f, .start_edge = 0 };
        poly_position(&g, &origin, 0, 0, 0);

        poly_root = &g;
        poly_min[0] = poly_min[1] = 0;
        poly_max[0] = poly_max[1] = 0;

        poly_t * iter = &g;
        int poly_count = 0;
        group_count++;

        if (debug) fprintf(stderr, "****** %d: New group %p\n",
            group_count, poly_root);

        while (iter)
        {
            poly_build(iter);
            iter = iter->work_next;
            poly_count++;
        }

        fprintf(stderr, "group %d: %d triangles\n",
            group_count, poly_count);

        float off_x = last_x - poly_min[0];
        float off_y = last_y - poly_min[1];
        last_y = off_y + poly_max[1];

        printf("<g transform=\"translate(%f %f)\">\n", off_x, off_y);
        poly_print(&g);
        printf("</g>\n");
    }

    printf("</svg>\n");
    free(faces);
    free(buf);

    return 0;
}