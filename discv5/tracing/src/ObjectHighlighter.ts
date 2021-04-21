import * as THREE from 'three';

export class ObjectHighlighter {
    readonly scene: THREE.Scene;
    private highlightedIds: Array<string>;

    constructor(scene: THREE.Scene) {
        this.scene = scene;
        this.highlightedIds = [];
    }

    highlight(intersects) {
        let obj = undefined;
        if (intersects.length > 0) {
            obj = this.scene.getObjectById(intersects[0].object.id);
        }

        let revertId = this.highlightedIds.shift();
        while (revertId !== undefined) {
            if (obj !== undefined && revertId === obj.id) {
                revertId = this.highlightedIds.shift();
                continue;
            }
            this.revert(revertId);
            revertId = this.highlightedIds.shift();
        }

        if (obj !== undefined && this.invert(obj.id)) {
            this.highlightedIds.push(obj.id);
        }
    }

    private invert(objectId) {
        const obj = this.scene.getObjectById(objectId) as THREE.Mesh;

        if (obj.userData.originalColor === undefined) {
            return false
        }

        const material = obj.material as THREE.MeshBasicMaterial;
        material.color.setHex(obj.userData.originalColor ^ 0xffffff);
        return true;
    }

    private revert(objectId) {
        const obj = this.scene.getObjectById(objectId) as THREE.Mesh;

        if (obj.userData.originalColor === undefined) {
            return;
        }

        const material = obj.material as THREE.MeshBasicMaterial;
        material.color.setHex(obj.userData.originalColor);
    }
}
