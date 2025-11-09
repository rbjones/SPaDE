#!/bin/bash
# Push locally saved SPaDE container to GitHub Container Registry
# Simplified version based on ProofPower container workflow pattern

set -e

echo "=== Push SPaDE Container to GHCR ==="

# Configuration
LOCAL_IMAGE="spade-saved:20251108-1303"
REGISTRY="ghcr.io"
USERNAME="rbjones"
IMAGE_NAME="spade"
REMOTE_IMAGE="${REGISTRY}/${USERNAME}/${IMAGE_NAME}:latest"

# Check local image exists
if ! docker image inspect "$LOCAL_IMAGE" &>/dev/null; then
    echo "Error: Image '$LOCAL_IMAGE' not found"
    echo "Available spade images:"
    docker images | grep spade || echo "  (none)"
    exit 1
fi

echo "Local image: $LOCAL_IMAGE"
echo "Remote image: $REMOTE_IMAGE"
echo ""

# Tag for GHCR
echo "Tagging image..."
docker tag "$LOCAL_IMAGE" "$REMOTE_IMAGE"

# Login to GHCR
echo ""
echo "Logging in to GitHub Container Registry..."
echo "You need a GitHub Personal Access Token with 'write:packages' scope"
echo "Create at: https://github.com/settings/tokens"
echo ""
docker login "$REGISTRY" -u "$USERNAME"

if [ $? -ne 0 ]; then
    echo "Login failed"
    exit 1
fi

# Push image
echo ""
echo "Pushing image (this will take a few minutes)..."
docker push "$REMOTE_IMAGE"

if [ $? -eq 0 ]; then
    echo ""
    echo "✓ Success! Container pushed to: $REMOTE_IMAGE"
    echo ""
    echo "To make it public:"
    echo "  https://github.com/users/$USERNAME/packages/container/$IMAGE_NAME/settings"
    echo ""
    echo "GitHub Actions can now use: ghcr.io/$USERNAME/$IMAGE_NAME:latest"
else
    echo "Push failed"
    exit 1
fi
