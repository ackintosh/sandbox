import * as THREE from 'three';

export class ObjectHighlighter {
    readonly scene: THREE.Scene;
    private highlightedIds: Array<number>;

    constructor(scene: THREE.Scene) {
        this.scene = scene;
        this.highlightedIds = [];
    }

    highlight(intersects): THREE.Object3D | null {
        let obj = undefined;
        if (intersects.length > 0) {
            obj = this.scene.getObjectById(intersects[0].object.id);
        }

        // Revert all highlighted objects
        let revertId = this.highlightedIds.shift();
        while (revertId !== undefined) {
            this.revert(revertId);
            revertId = this.highlightedIds.shift();
        }

        if (obj !== undefined && this.invert(obj.id)) {
            this.highlightedIds.push(obj.id);
            return obj;
        }

        return null;
    }

    private invert(objectId: number): boolean {
        const obj = this.scene.getObjectById(objectId) as THREE.Mesh;

        if (obj.userData.originalColor === undefined) {
            return false
        }

        const material = obj.material as THREE.MeshBasicMaterial;
        material.color.setHex(obj.userData.originalColor ^ 0xffffff);
        return true;
    }

    private revert(objectId: number): void {
        const obj = this.scene.getObjectById(objectId) as THREE.Mesh;

        if (obj.userData.originalColor === undefined) {
            return;
        }

        const material = obj.material as THREE.MeshBasicMaterial;
        material.color.setHex(obj.userData.originalColor);
    }
}
