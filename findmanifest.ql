import java
import codeql.xml.Xml
import semmle.code.xml.AndroidManifest


from AndroidManifestXmlFile manifest, AndroidComponentXmlElement component, string permNeeded
where 
    component.getFile() = manifest and
    component.isExported() and
    component.requiresPermissions() and
    permNeeded = component.getAnAttribute().(AndroidPermissionXmlAttribute).getValue()
select
    manifest.getAbsolutePath() as filepath,
    component.getName() as type,
    component.getResolvedComponentName() as name,
    permNeeded as permissionNeeded
